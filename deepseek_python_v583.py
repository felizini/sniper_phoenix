#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
PHOENIX REAL v5.8.3 - CORREÇÕES DE ESTADO E RANGE TRADING MODE
- Correção: salvamento de estado após atualização das flags de posição
- Aumento do mínimo de candles para ADX (30)
- Validação de notional mínimo em vendas
- Atualização de maxPrice no modo range
- Melhorias gerais de estabilidade
"""

import ccxt
import pandas as pd
import numpy as np
import time
import configparser
import os
import sys
import threading
from datetime import datetime, timedelta
from colorama import Fore, init
import signal
import asyncio
import websockets
import json
import logging
import logging.handlers
import csv
from collections import deque
from typing import Optional, Dict, Any, List

init(autoreset=True)
inicio_bot = datetime.now()

# --- ARQUIVOS ---
ARQUIVO_ESTADO      = "sniper_state.json"
ARQUIVO_LOG_SISTEMA = "sniper_system.log"
ARQUIVO_LOG_TRADES  = "sniper_trades.csv"

# --- LOCKS ---
state_lock    = threading.Lock()
config_lock   = threading.Lock()
engine_lock   = threading.RLock()
csv_lock      = threading.Lock()
exchange_lock = threading.Lock()

TRIGGER_TOLERANCE = 0.001

# =============================================================================
# FUNÇÕES AUXILIARES
# =============================================================================

def safe_div(a: float, b: float, default: float = 0.0) -> float:
    return a / b if b != 0 else default

# =============================================================================
# INDICADORES TÉCNICOS (pandas)
# =============================================================================

def compute_ema(prices: List[float], period: int) -> List[float]:
    s = pd.Series(prices)
    return s.ewm(span=period, adjust=False).mean().tolist()

def compute_rsi(prices: List[float], period: int = 14) -> List[float]:
    if len(prices) < period + 1:
        return [50.0] * len(prices)
    s = pd.Series(prices)
    delta = s.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.rolling(window=period, min_periods=period).mean()
    avg_loss = loss.rolling(window=period, min_periods=period).mean()
    rsi = pd.Series(index=s.index, dtype=float)
    for i in range(period, len(prices)):
        ag = avg_gain.iloc[i]
        al = avg_loss.iloc[i]
        if al == 0:
            rsi.iloc[i] = 100.0 if ag > 0 else 50.0
        else:
            rs = ag / al
            rsi.iloc[i] = 100.0 - (100.0 / (1.0 + rs))
    rsi.iloc[:period] = 50.0
    return rsi.fillna(50).tolist()

def compute_atr_incremental(prev_atr: float, high: float, low: float, close: float,
                            prev_close: float, period: int) -> float:
    tr = max(high - low, abs(high - prev_close), abs(low - prev_close))
    alpha = 2.0 / (period + 1)
    return alpha * tr + (1 - alpha) * prev_atr

def compute_bollinger_bands(prices: List[float], period: int = 20, std_dev: float = 2.0):
    if len(prices) < period:
        return None, None, None
    s = pd.Series(prices[-period:])
    sma = s.mean()
    std = s.std()
    return sma + (std * std_dev), sma - (std * std_dev), sma

def compute_adx(high: List[float], low: List[float], close: List[float], period: int = 14) -> float:
    """
    Retorna o valor ADX atual baseado nos últimos 'period' candles.
    Requer listas com pelo menos period+1 elementos.
    """
    if len(high) < period + 1 or len(low) < period + 1 or len(close) < period + 1:
        return 0.0
    plus_dm = []
    minus_dm = []
    tr = []
    for i in range(1, len(high)):
        h = high[i]
        l = low[i]
        prev_h = high[i-1]
        prev_l = low[i-1]
        prev_c = close[i-1]
        # True Range
        tr.append(max(h - l, abs(h - prev_c), abs(l - prev_c)))
        # Directional Movement
        up_move = h - prev_h
        down_move = prev_l - l
        if up_move > down_move and up_move > 0:
            plus_dm.append(up_move)
        else:
            plus_dm.append(0)
        if down_move > up_move and down_move > 0:
            minus_dm.append(down_move)
        else:
            minus_dm.append(0)
    # Smooth using Wilder's method (EMA with alpha = 1/period)
    tr_smooth = [sum(tr[:period])]
    plus_dm_smooth = [sum(plus_dm[:period])]
    minus_dm_smooth = [sum(minus_dm[:period])]
    for i in range(period, len(tr)):
        tr_smooth.append(tr_smooth[-1] - tr_smooth[-1]/period + tr[i])
        plus_dm_smooth.append(plus_dm_smooth[-1] - plus_dm_smooth[-1]/period + plus_dm[i])
        minus_dm_smooth.append(minus_dm_smooth[-1] - minus_dm_smooth[-1]/period + minus_dm[i])
    # Calculate +DI and -DI
    plus_di = [100 * p / t if t != 0 else 0 for p, t in zip(plus_dm_smooth, tr_smooth)]
    minus_di = [100 * m / t if t != 0 else 0 for m, t in zip(minus_dm_smooth, tr_smooth)]
    # DX = |+DI - -DI| / (+DI + -DI) * 100
    dx = []
    for p, m in zip(plus_di, minus_di):
        if p + m == 0:
            dx.append(0)
        else:
            dx.append(abs(p - m) / (p + m) * 100)
    # ADX = EMA of DX over period
    if len(dx) < period:
        return 0.0
    adx = sum(dx[:period]) / period
    for i in range(period, len(dx)):
        adx = (adx * (period - 1) + dx[i]) / period
    return adx

# =============================================================================
# MTF SIGNALS (0..3)
# =============================================================================

def build_mtf_signals(closes: List[float]) -> List[int]:
    n = len(closes)
    if n < 100:
        return [0] * n
    ema25 = compute_ema(closes, 25)
    ema50 = compute_ema(closes, 50)
    ema100 = compute_ema(closes, 100)
    signals = [0] * n
    for i in range(n):
        cnt = 0
        if closes[i] > ema25[i]: cnt += 1
        if closes[i] > ema50[i]: cnt += 1
        if closes[i] > ema100[i]: cnt += 1
        signals[i] = cnt
    return signals

# =============================================================================
# REGIME DE MERCADO (apenas para exibição)
# =============================================================================

REGIME_SEVERITY = {"RALLY": 4, "LATERAL": 3, "STANDBY": 2, "DOWNTREND": 1, "TOP": 0}

def compute_regime_simple(closes: List[float], rsi: float) -> str:
    if len(closes) < 50:
        return "STANDBY"
    ema20 = compute_ema(closes, 20)[-1]
    ema50 = compute_ema(closes, 50)[-1]
    price = closes[-1]
    if rsi > 75: return "TOP"
    if price < ema20 and ema20 < ema50 and rsi < 40: return "DOWNTREND"
    if price > ema20 and ema20 > ema50 and 50 <= rsi <= 70: return "RALLY"
    if abs(safe_div(ema20, ema50) - 1) < 0.02 and 40 <= rsi <= 60: return "LATERAL"
    return "STANDBY"

# =============================================================================
# FUNÇÃO DE VENDA (com validação de notional mínimo)
# =============================================================================

def vender_quantidade(exchange, qtd: float, custo: float, motivo: str, config: Dict,
                      shared_state: Dict, state_lock, cash_var) -> Dict:
    symbol = config["SYMBOL"]
    try:
        base_currency = symbol.split('/')[0]
        with exchange_lock:
            real_balance = exchange.fetch_balance()[base_currency]['free']
        if qtd > real_balance:
            qtd = real_balance
            if qtd <= 0:
                return {'ok': False, 'msg': 'Saldo zero'}
        with exchange_lock:
            market = exchange.market(symbol)
            min_amount = market['limits']['amount']['min']
            min_notional = market['limits']['cost']['min']
        with exchange_lock:
            qtd_fmt = exchange.amount_to_precision(symbol, qtd)
            qtd_rounded = float(qtd_fmt)
        if qtd_rounded < min_amount:
            return {'ok': False, 'msg': f'Qtd {qtd_rounded} abaixo do mínimo {min_amount}'}
        # Obter preço atual estimado (usando ticker) para verificar notional
        with exchange_lock:
            ticker = exchange.fetch_ticker(symbol)
            preco_est = ticker['last']
        if qtd_rounded * preco_est < min_notional:
            return {'ok': False, 'msg': f'Valor total estimado {qtd_rounded * preco_est:.2f} abaixo do mínimo {min_notional}'}
        with exchange_lock:
            ordem = exchange.create_order(symbol, 'market', 'sell', qtd_fmt)
            preco = float(ordem.get('average') or ordem.get('price') or 0)
            receita = float(ordem.get('cost') or 0)
        pnl = receita - custo
        pnl_pct = safe_div(pnl, custo) * 100
        return {'ok': True, 'preco': preco, 'receita': receita, 'pnl': pnl, 'pnl_pct': pnl_pct}
    except Exception as e:
        logging.error(f"Erro na venda ({motivo}): {e}")
        return {'ok': False, 'msg': str(e)}

# =============================================================================
# MOTOR DCA COM RANGE TRADING MODE (CORRIGIDO)
# =============================================================================

class DCAEngineBacktest:
    def __init__(self, config: Dict, exchange, state_lock, shared_state):
        self.config = config
        self.exchange = exchange
        self.state_lock = state_lock
        self.shared_state = shared_state
        self.accumulated_profit = 0.0

        # Parâmetros fixos
        self.base_cfg = {
            "capital_base": config["CAPITAL_BASE"],
            "max_safety_orders": config["MAX_SAFETY_ORDERS"],
            "dca_vol_scale": config["DCA_VOLUME_SCALE"],
            "dca_step_initial": config["DCA_STEP_INITIAL"],
            "dca_step_scale": config["DCA_STEP_SCALE"],
            "trailing_trigger": config["TRAILING_TRIGGER"],
            "trailing_dist": config["TRAILING_DIST"],
            "stop_loss": config["STOP_LOSS"],
            "compound": config["COMPOUND"],
        }

        self.position = None
        self.cash = config["CAPITAL_TOTAL"]
        self.cooldown = 0
        self.current_regime = "STANDBY"
        self.last_candle_time = 0

        self.price_history = deque(maxlen=500)
        self.price_history_high = deque(maxlen=500)
        self.price_history_low = deque(maxlen=500)
        self.volume_history = deque(maxlen=500)
        self.candles_history = deque(maxlen=200)

        self.atr_value = 0.0
        self.atr_period = config.get("ATR_PERIOD", 14)
        self.last_close_for_atr = None
        self.atr_history = deque(maxlen=100)

        self.chandelier_enabled = config.get("CHANDELIER_ENABLED", True)
        self.chandelier_factor = config.get("CHANDELIER_FACTOR", 3.0)

        self._partial_sold_levels = set()

        symbol = config["SYMBOL"]
        if exchange:
            try:
                market = exchange.market(symbol)
                self.min_notional = market['limits']['cost']['min']
            except Exception:
                self.min_notional = 5.0
        else:
            self.min_notional = 5.0

        # Range Trading Mode
        self.range_mode_enabled = config.get("RANGE_MODE_ENABLED", False)
        self.adx_threshold = config.get("RANGE_ADX_THRESHOLD", 20)
        self.bb_period = config.get("RANGE_BB_PERIOD", 20)
        self.bb_std = config.get("RANGE_BB_STD", 2.0)
        self.rsi_oversold = config.get("RANGE_RSI_OVERSOLD", 35)
        self.rsi_overbought = config.get("RANGE_RSI_OVERBOUGHT", 65)
        self.range_tp_pct = config.get("RANGE_TAKE_PROFIT_PCT", 0.01)
        self.range_sl_pct = config.get("RANGE_STOP_LOSS_PCT", 0.005)
        self.range_use_band_exit = config.get("RANGE_USE_BAND_EXIT", True)
        self.is_ranging = False

    def _active_params(self):
        return self.base_cfg

    def _effective_capital_base(self, current_price):
        if not self.base_cfg["compound"]:
            return self.base_cfg["capital_base"]
        nova_entrada = self.base_cfg["capital_base"] + self.accumulated_profit
        return min(nova_entrada, self.cash)

    def _update_atr(self, high, low, close):
        if self.last_close_for_atr is None:
            self.last_close_for_atr = close
            self.atr_value = 0.0
            return
        self.atr_value = compute_atr_incremental(self.atr_value, high, low, close,
                                                 self.last_close_for_atr, self.atr_period)
        self.last_close_for_atr = close
        atr_pct = safe_div(self.atr_value, close)
        self.atr_history.append(atr_pct)

    def _initialize_atr(self, candles):
        if len(candles) < self.atr_period:
            return
        tr_values = []
        for i in range(1, self.atr_period + 1):
            high = candles[-i]['h']
            low  = candles[-i]['l']
            close_prev = candles[-i-1]['c']
            tr = max(high - low, abs(high - close_prev), abs(low - close_prev))
            tr_values.append(tr)
        self.atr_value = sum(tr_values) / self.atr_period
        self.last_close_for_atr = candles[-1]['c']
        atr_pct = safe_div(self.atr_value, self.last_close_for_atr)
        self.atr_history.append(atr_pct)

    def _update_market_regime(self, high, low, close):
        """Atualiza self.is_ranging baseado no ADX (requer pelo menos 30 candles)."""
        if not self.range_mode_enabled:
            self.is_ranging = False
            return
        # Usar ADX apenas com dados suficientes (mínimo 30 candles para estabilidade)
        if len(self.price_history) >= 30:
            highs = list(self.price_history_high)
            lows = list(self.price_history_low)
            closes = list(self.price_history)
            adx = compute_adx(highs, lows, closes, period=14)
            self.is_ranging = adx < self.adx_threshold
        else:
            # Fallback: largura das Bandas de Bollinger (precisa de pelo menos 20)
            if len(self.price_history) >= 20:
                upper, lower, mid = compute_bollinger_bands(list(self.price_history), self.bb_period, self.bb_std)
                if upper and lower and mid:
                    width = (upper - lower) / mid
                    self.is_ranging = width < 0.03
                else:
                    self.is_ranging = False
            else:
                self.is_ranging = False

    def _open_position(self, price, time_ms, entry_details: dict = None):
        cost = self._effective_capital_base(price)
        if self.cash < cost:
            return False

        obs = "Entrada"
        if entry_details:
            parts = []
            if "score" in entry_details:
                parts.append(f"score={entry_details['score']}")
            if "mtf" in entry_details:
                parts.append(f"MTF={entry_details['mtf']}")
            if "vol_score" in entry_details:
                parts.append(f"vol_score={entry_details['vol_score']}")
            if "rsi" in entry_details:
                parts.append(f"RSI={entry_details['rsi']}")
            if "vol_ratio" in entry_details:
                parts.append(f"vol_ratio={entry_details['vol_ratio']}")
            if "regime" in entry_details:
                parts.append(f"regime={entry_details['regime']}")
            if "lower_band" in entry_details:
                parts.append(f"lower_band={entry_details['lower_band']}")
            if "upper_band" in entry_details:
                parts.append(f"upper_band={entry_details['upper_band']}")
            obs = " | ".join(parts)
        ordem = comprar_com_vault(cost, motivo=obs)

        if not ordem['ok']:
            return False
        qty = ordem['v']
        custo_real = ordem['c']
        preco_real = ordem['p']
        self.cash -= custo_real
        self.position = {
            "entries": [{"price": preco_real, "qty": qty, "cost": custo_real, "time": time_ms}],
            "totalQty": qty,
            "totalCost": custo_real,
            "avgCost": preco_real,
            "soUsed": 0,
            "trailActive": False,
            "maxPrice": preco_real,
            "trailStop": 0.0,
            "sl_price": None,
            "openTime": time_ms,
            "entryRegime": self.current_regime,
            "nextDCAPrice": preco_real * (1 - self._active_params()["dca_step_initial"]),
            "nextDCACost": custo_real * self._active_params()["dca_vol_scale"],
            "maxProfitPct": 0.0,
            "candles_since_last_high": 0
        }
        with self.state_lock:
            self.shared_state["em_operacao"] = True
            self.shared_state["marcha"] = "DCA ATIVO"
            self.shared_state["high_intrabar"] = price
            self.shared_state["high_intrabar_timestamp"] = time_ms
        salvar_estado_disco()
        return True

    def _add_safety_order(self, price, time_ms):
        with self.state_lock:
            if self.shared_state.get("operating_paused", False):
                return False
        if self.position["soUsed"] >= self._active_params()["max_safety_orders"]:
            return False
        cost = self.position["nextDCACost"]
        if self.cash < cost:
            return False
        ordem = comprar_com_vault(cost, motivo=f"DCA #{self.position['soUsed']+1}")
        if not ordem['ok']:
            return False
        qty = ordem['v']
        custo_real = ordem['c']
        preco_real = ordem['p']
        self.cash -= custo_real
        self.position["entries"].append({"price": preco_real, "qty": qty, "cost": custo_real, "time": time_ms})
        self.position["totalQty"] += qty
        self.position["totalCost"] += custo_real
        self.position["avgCost"] = safe_div(self.position["totalCost"], self.position["totalQty"])
        self.position["soUsed"] += 1

        step_init = self._active_params()["dca_step_initial"]
        step_scale = self._active_params()["dca_step_scale"]
        self.position["nextDCAPrice"] = preco_real * (1 - step_init * (step_scale ** self.position["soUsed"]))
        self.position["nextDCACost"] = cost * self._active_params()["dca_vol_scale"]
        self.position["trailActive"] = False
        self.position["maxPrice"] = preco_real
        salvar_estado_disco()
        return True

    def _close_position(self, exit_price, time_ms, reason):
        if self.position is None:
            return False
        qtd = self.position["totalQty"]
        custo = self.position["totalCost"]
        pos = self.position
        params = self._active_params()

        if pos["avgCost"] <= 0:
            logging.error(f"avgCost inválido: {pos['avgCost']}")
            return False
        current_profit_pct = safe_div((exit_price - pos["avgCost"]), pos["avgCost"]) * 100

        obs = f"{reason} | profit={current_profit_pct:.2f}%"
        if reason in ("CHANDELIER_STOP", "TRAILING_STOP"):
            obs += f" | atr={self.atr_value:.6f} | factor={self.chandelier_factor if self.chandelier_enabled else 'N/A'}"
            if pos.get("trailStop"):
                obs += f" | stop={pos['trailStop']:.6f}"
        elif reason == "STOP_LOSS":
            sl_price = pos["avgCost"] * (1 - params["stop_loss"])
            obs += f" | sl_pct={params['stop_loss']*100:.2f}% | sl_price={sl_price:.6f}"
        elif reason.startswith("MAX_HOLD"):
            max_hours = self.config.get("MAX_HOLD_HOURS", 0)
            obs += f" | max_hours={max_hours}"
        elif reason in ("RANGE_BAND_TOP", "RANGE_TP", "RANGE_STOP_LOSS"):
            obs += f" | range_mode=True"

        res = vender_quantidade(self.exchange, qtd, custo, obs, self.config,
                                self.shared_state, self.state_lock, self.cash)
        if res['ok']:
            self.cash += res['receita']
            self.accumulated_profit += res['pnl']
            recolher_para_fundos()
            Auditoria.log_transacao(
                tipo="VENDA",
                preco=res['preco'],
                qtd=qtd,
                total_usd=res['receita'],
                lucro_usd=res['pnl'],
                lucro_perc=res['pnl_pct'],
                saldo_vault=self.cash,
                obs=obs
            )
            # --- LIMPEZA DA POSIÇÃO E ESTADO ---
            self.position = None
            self.cooldown = self.config["ENTRY_COOLDOWN"]
            with self.state_lock:
                self.shared_state["em_operacao"] = False
                self.shared_state["trailing_ativo"] = False
                self.shared_state["max_p_trailing"] = 0.0
                self.shared_state["high_intrabar"] = 0.0
                self.shared_state["high_intrabar_timestamp"] = 0
            self._partial_sold_levels.clear()
            salvar_estado_disco()   # SALVAR APÓS ATUALIZAR FLAGS
            return True
        else:
            logging.error(f"Falha na venda ({reason}): {res.get('msg')}")
            if "abaixo do mínimo" in res.get('msg', ''):
                self.position = None
                with self.state_lock:
                    self.shared_state["em_operacao"] = False
                    self.shared_state["trailing_ativo"] = False
                    self.shared_state["max_p_trailing"] = 0.0
                    self.shared_state["high_intrabar"] = 0.0
                    self.shared_state["high_intrabar_timestamp"] = 0
                salvar_estado_disco()
                return False
            return False

    def _partial_close(self, qty, price, time_ms, reason, triggered_levels=None):
        if self.position is None or qty <= 0:
            return False, False
        qty = min(qty, self.position["totalQty"])
        if self.position["totalQty"] <= 0:
            return False, False
        custo_proporcional = self.position["totalCost"] * safe_div(qty, self.position["totalQty"])
        res = vender_quantidade(self.exchange, qty, custo_proporcional, reason,
                                self.config, self.shared_state, self.state_lock, self.cash)
        if not res['ok']:
            return False, False
        self.cash += res['receita']
        self.accumulated_profit += res['pnl']
        recolher_para_fundos()

        obs = reason
        if reason == "TP_MULTI" and triggered_levels:
            obs += f" | levels={','.join(map(str, triggered_levels))}%"
        current_profit_pct = safe_div((price - self.position["avgCost"]), self.position["avgCost"]) * 100
        obs += f" | profit={current_profit_pct:.2f}%"

        Auditoria.log_transacao(
            tipo="VENDA",
            preco=res['preco'],
            qtd=qty,
            total_usd=res['receita'],
            lucro_usd=res['pnl'],
            lucro_perc=res['pnl_pct'],
            saldo_vault=self.cash,
            obs=obs
        )

        self.position["totalQty"] -= qty
        self.position["totalCost"] -= custo_proporcional
        if self.position["totalQty"] < 1e-10:
            # Fechamento total
            self.position = None
            with self.state_lock:
                self.shared_state["em_operacao"] = False
                self.shared_state["trailing_ativo"] = False
                self.shared_state["max_p_trailing"] = 0.0
            self._partial_sold_levels.clear()
            self.cooldown = self.config["ENTRY_COOLDOWN"]
            salvar_estado_disco()
            return True, True
        else:
            self.position["avgCost"] = safe_div(self.position["totalCost"], self.position["totalQty"])
            salvar_estado_disco()
        return False, True

    def on_candle(self, candle: Dict):
        open_p = candle['o']
        high = candle['h']
        low = candle['l']
        close = candle['c']
        volume = candle['v']
        time_ms = candle['t']

        self.last_candle_time = time_ms
        self.price_history.append(close)
        self.price_history_high.append(high)
        self.price_history_low.append(low)
        self.volume_history.append(volume)

        if len(self.price_history) >= 50:
            closes = list(self.price_history)
            rsi = compute_rsi(closes, self.config["RSI_PERIOD"])[-1]
            self.current_regime = compute_regime_simple(closes, rsi)
            with self.state_lock:
                self.shared_state["current_regime"] = self.current_regime
                self.shared_state["rsi_atual"] = rsi

        self.candles_history.append({
            'o': open_p, 'h': high, 'l': low, 'c': close, 'v': volume, 't': time_ms
        })

        if self.atr_value == 0.0 and len(self.candles_history) >= self.atr_period + 1:
            self._initialize_atr(list(self.candles_history))

        self._update_atr(high, low, close)

        # Atualiza regime de mercado
        self._update_market_regime(high, low, close)

        if self.cooldown > 0:
            self.cooldown -= 1

        if self.position is None:
            self._check_entry(open_p, time_ms, close, high, low, volume)
        else:
            self._manage_position(high, low, close, time_ms, volume)

    def _check_entry_trend(self, price, time_ms, close, high, low, volume, rsi):
        """Estratégia original de tendência (MTF + volume)"""
        if self.cooldown > 0:
            return
        with self.state_lock:
            if self.shared_state.get("operating_paused", False):
                return
            if self.shared_state.get("circuit_breaker", False):
                return
            if self.shared_state.get("spike_active", False):
                return
        if self.cash < self._effective_capital_base(price):
            return

        regime = self.current_regime

        # MTF (0..3)
        mtf_val = 0
        if len(self.price_history) >= 100:
            closes = list(self.price_history)
            mtf_val = build_mtf_signals(closes)[-1]
        score = mtf_val
        max_score = 3

        # Volume (0..2)
        vol_score = 0.0
        vol_ratio = 0.0
        if len(self.volume_history) >= 20:
            vol_media = sum(list(self.volume_history)[-20:]) / 20
            if vol_media > 0:
                vol_ratio = volume / vol_media
                min_ratio = self.config["VOLUME_FATOR_MIN"]
                if vol_ratio >= min_ratio:
                    vol_score = min(2.0, (vol_ratio - min_ratio) * 2)
        score += vol_score
        max_score += 2

        # Penalidade por RSI
        penalty = 0.0
        rsi_max = self.config["RSI_MAX_ENTRADA"]
        if rsi > rsi_max:
            excess = (rsi - rsi_max) / 10.0
            penalty += min(1.0, excess)

        # Penalidade por regime desfavorável
        if self.config.get("REGIME_SAFE_MODE", True) and regime in ("DOWNTREND", "TOP"):
            penalty += 0.4

        total_score = max(0.0, score - penalty)
        normalized_score = safe_div(total_score, max_score)
        threshold = self.config.get("ENTRY_SCORE_THRESHOLD", 0.75)

        self.shared_state["entry_score"] = normalized_score
        self.shared_state["entry_score_threshold"] = threshold

        if normalized_score < threshold:
            return

        entry_details = {
            "score": f"{total_score:.2f}/{max_score:.0f} (norm: {normalized_score:.2f})",
            "mtf": f"{mtf_val}/3",
            "vol_score": f"{vol_score:.1f}/2",
            "rsi": f"{rsi:.1f}",
            "vol_ratio": f"{vol_ratio:.2f}",
            "regime": regime,
        }
        self._open_position(price, time_ms, entry_details)

    def _check_entry_range(self, price, time_ms, close, high, low, volume, rsi):
        """Estratégia de reversão à média (Range Trading Mode)"""
        if len(self.price_history) < self.bb_period:
            return
        upper, lower, mid = compute_bollinger_bands(list(self.price_history), self.bb_period, self.bb_std)
        if upper is None or lower is None:
            return
        # Condição de compra: preço <= banda inferior e RSI sobrevendido
        if close <= lower and rsi <= self.rsi_oversold:
            if self.position is None and self.cooldown == 0:
                entry_details = {
                    "score": "Range mode (BB lower)",
                    "rsi": f"{rsi:.1f}",
                    "lower_band": f"{lower:.6f}",
                    "upper_band": f"{upper:.6f}",
                    "regime": "RANGE"
                }
                self._open_position(price, time_ms, entry_details)
                return True
        return False

    def _check_entry(self, price, time_ms, close, high, low, volume):
        rsi = self.shared_state.get("rsi_atual", 50)
        if self.is_ranging and self.range_mode_enabled:
            self._check_entry_range(price, time_ms, close, high, low, volume, rsi)
        else:
            self._check_entry_trend(price, time_ms, close, high, low, volume, rsi)

    def _manage_position(self, high, low, close, time_ms, volume):
        if self.position is None:
            return
        if self.position["avgCost"] < 1e-10:
            self._close_position(close, time_ms, "AVGCOST_ZERO")
            return

        # Se estiver em modo range, gerencia com regras específicas
        if self.is_ranging and self.range_mode_enabled:
            # Atualizar máximo e contador de velas sem新高 (importante para consistência)
            if high > self.position["maxPrice"]:
                self.position["maxPrice"] = high
                self.position["candles_since_last_high"] = 0
            else:
                self.position["candles_since_last_high"] += 1

            # Saída por take profit fixo ou banda superior
            upper, lower, _ = compute_bollinger_bands(list(self.price_history), self.bb_period, self.bb_std)
            if upper:
                tp_price = self.position["avgCost"] * (1 + self.range_tp_pct)
                if self.range_use_band_exit and close >= upper:
                    self._close_position(close, time_ms, "RANGE_BAND_TOP")
                    return
                elif close >= tp_price:
                    self._close_position(close, time_ms, "RANGE_TP")
                    return
            # Stop loss
            sl_price = self.position["avgCost"] * (1 - self.range_sl_pct)
            if low <= sl_price:
                self._close_position(sl_price, time_ms, "RANGE_STOP_LOSS")
                return
            # Se nenhuma condição de saída, mantém a posição (sem trailing, sem DCA)
            return

        # Modo tendência (original)
        preco_atual = self.shared_state.get("preco", 0)
        if preco_atual <= 0:
            try:
                with exchange_lock:
                    ticker = self.exchange.fetch_ticker(self.config["SYMBOL"])
                    preco_atual = ticker['last']
                    with self.state_lock:
                        self.shared_state["preco"] = preco_atual
            except Exception:
                preco_atual = close
        if preco_atual <= 0:
            return

        if self.position["totalQty"] * close < self.min_notional:
            logging.error(f"Notional invendável ({self.position['totalQty'] * close:.2f} < {self.min_notional}). Descartando posição.")
            self.position = None
            with self.state_lock:
                self.shared_state["em_operacao"] = False
                self.shared_state["trailing_ativo"] = False
                self.shared_state["max_p_trailing"] = 0.0
            salvar_estado_disco()
            return

        # Take profit parcial
        tp_levels = self.config.get("TAKE_PROFIT_LEVELS", [])
        tp_sizes = self.config.get("TAKE_PROFIT_SIZES", [])
        if tp_levels and tp_sizes and self.position["avgCost"] > 0:
            current_profit_pct = safe_div((close - self.position["avgCost"]), self.position["avgCost"])
            total_sell_qty = 0
            triggered_levels = []
            for i, level in enumerate(tp_levels):
                if level not in self._partial_sold_levels and current_profit_pct >= level / 100.0:
                    total_sell_qty += self.position["totalQty"] * tp_sizes[i]
                    triggered_levels.append(level)
            if total_sell_qty > 0:
                if total_sell_qty * close < self.min_notional:
                    total_sell_qty = self.position["totalQty"]
                fully_closed, success = self._partial_close(total_sell_qty, close, time_ms, "TP_MULTI", triggered_levels)
                if fully_closed:
                    return

        pos = self.position
        params = self._active_params()

        if high > pos["maxPrice"]:
            pos["maxPrice"] = high
            pos["candles_since_last_high"] = 0
        else:
            pos["candles_since_last_high"] += 1

        current_profit_pct = safe_div((close - pos["avgCost"]), pos["avgCost"])
        if current_profit_pct > pos["maxProfitPct"]:
            pos["maxProfitPct"] = current_profit_pct

        # Exit score
        exit_score = 0.0
        drawdown_pct = safe_div((pos["maxPrice"] - close), pos["maxPrice"]) * 100
        exit_score += min(3.0, drawdown_pct)

        if pos.get("trailActive", False) and low <= pos.get("trailStop", 0):
            exit_score += 3.0

        # Volume dump
        if self.config.get("VOLUME_DUMP_EXIT", False) and len(self.volume_history) >= 21:
            vol_avg = sum(list(self.volume_history)[-21:-1]) / 20
            vol_ratio = volume / vol_avg if vol_avg > 0 else 0
            if vol_ratio >= self.config.get("VOLUME_DUMP_MULTIPLIER", 3.5):
                confirm = self.config.get("VOLUME_DUMP_CONFIRM_CANDLES", 2)
                if len(self.candles_history) >= confirm:
                    recent = list(self.candles_history)[-confirm:]
                    drop_pct = self.config.get("VOLUME_DUMP_DROP_PCT", 0.6) / 100.0
                    if all(c['c'] < c['o'] * (1 - drop_pct) for c in recent):
                        exit_score += 1.5

        # Estagnação
        if self.config.get("STAGNATION_EXIT", True) and pos["maxProfitPct"] >= self.config.get("MIN_PROFIT_PCT", 0.008):
            if pos["candles_since_last_high"] >= self.config.get("MAX_CANDLES_NO_HIGH", 45):
                exit_score += 1.0

        # Stop loss breach
        sl_price = pos["avgCost"] * (1 - params["stop_loss"])
        if low <= sl_price * (1 + TRIGGER_TOLERANCE):
            exit_score += 5.0

        # EMA cross
        if self.config.get("EMA_CROSS_EXIT", True) and pos["maxProfitPct"] >= self.config.get("MIN_PROFIT_PCT_EMA", 0.008):
            closes = list(self.price_history)
            if len(closes) >= 10:
                ema3 = compute_ema(closes, 3)[-1]
                ema10 = compute_ema(closes, 10)[-1]
                ema3_prev = compute_ema(closes, 3)[-2]
                ema10_prev = compute_ema(closes, 10)[-2]
                if ema3_prev >= ema10_prev and ema3 < ema10:
                    exit_score += 1.0

        self.shared_state["exit_score"] = exit_score
        self.shared_state["exit_score_threshold"] = self.config.get("EXIT_SCORE_THRESHOLD", 8.5)
        if exit_score >= self.config.get("EXIT_SCORE_THRESHOLD", 8.5):
            self._close_position(close, time_ms, f"EXIT_SCORE_{exit_score:.1f}")
            return

        # Gerenciamento do trailing stop
        if self.chandelier_enabled and self.atr_value > 0:
            if pos["trailActive"]:
                new_stop = pos["maxPrice"] - (self.chandelier_factor * self.atr_value)
                if new_stop > pos["trailStop"]:
                    pos["trailStop"] = new_stop
            else:
                trigger_price = pos["avgCost"] * (1 + params["trailing_trigger"])
                if high >= trigger_price * (1 - TRIGGER_TOLERANCE):
                    pos["trailActive"] = True
                    pos["trailStop"] = pos["maxPrice"] - (self.chandelier_factor * self.atr_value)
                    with self.state_lock:
                        self.shared_state["trailing_ativo"] = True
                    logging.info(f"Chandelier ativado: stop={pos['trailStop']:.8f}")
        else:
            if pos["trailActive"]:
                new_stop = pos["maxPrice"] * (1 - params["trailing_dist"])
                if new_stop > pos["trailStop"]:
                    pos["trailStop"] = new_stop
            else:
                trigger_price = pos["avgCost"] * (1 + params["trailing_trigger"])
                if high >= trigger_price * (1 - TRIGGER_TOLERANCE):
                    pos["trailActive"] = True
                    pos["trailStop"] = pos["maxPrice"] * (1 - params["trailing_dist"])
                    with self.state_lock:
                        self.shared_state["trailing_ativo"] = True
                    logging.info(f"Trailing ativado: stop={pos['trailStop']:.8f}")

        # Safety orders
        if not pos["trailActive"] and pos["soUsed"] < params["max_safety_orders"]:
            if low <= pos["nextDCAPrice"]:
                self._add_safety_order(pos["nextDCAPrice"], time_ms)

    def get_state(self):
        state = {
            "current_regime": self.current_regime,
            "cash": self.cash,
            "preco_medio": 0,
            "lucro_perc_atual": 0,
            "perda_usd_atual": 0,
            "num_safety_orders": 0,
            "proxima_compra_p": 0,
            "trailing_ativo": False,
            "max_p_trailing": 0,
            "stop_atual_trailing": 0,
            "alvo_trailing_ativacao": 0
        }
        if self.position:
            state["preco_medio"] = self.position["avgCost"]
            current_price = self.shared_state.get("preco", 0.0)
            if current_price <= 0:
                state["perda_usd_atual"] = 0.0
                state["lucro_perc_atual"] = 0.0
            else:
                state["lucro_perc_atual"] = (safe_div(current_price, self.position["avgCost"]) - 1) * 100
                state["perda_usd_atual"] = self.position["totalCost"] - (current_price * self.position["totalQty"])
            state["num_safety_orders"] = self.position["soUsed"]
            state["proxima_compra_p"] = self.position["nextDCAPrice"] if self.position["soUsed"] < self.base_cfg["max_safety_orders"] else 0
            state["trailing_ativo"] = self.position["trailActive"]
            state["max_p_trailing"] = self.position["maxPrice"]
            state["stop_atual_trailing"] = self.position.get("trailStop", 0)
            state["alvo_trailing_ativacao"] = self.position["avgCost"] * (1 + self.base_cfg["trailing_trigger"]) if not self.position["trailActive"] else 0
        return state

    def to_dict(self):
        return {
            "position": self.position,
            "cash": self.cash,
            "cooldown": self.cooldown,
            "current_regime": self.current_regime,
            "last_candle_time": self.last_candle_time,
            "atr_value": self.atr_value,
            "atr_history": list(self.atr_history),
            "last_close_for_atr": self.last_close_for_atr,
            "accumulated_profit": self.accumulated_profit,
            "partial_sold_levels": list(self._partial_sold_levels)
        }

    def from_dict(self, data):
        self.position = data.get("position")
        self.cash = data.get("cash", self.config["CAPITAL_TOTAL"])
        self.cooldown = data.get("cooldown", 0)
        self.current_regime = data.get("current_regime", "STANDBY")
        self.last_candle_time = data.get("last_candle_time", 0)
        self.atr_value = data.get("atr_value", 0.0)
        self.atr_history = deque(data.get("atr_history", []), maxlen=100)
        self.last_close_for_atr = data.get("last_close_for_atr")
        self.accumulated_profit = data.get("accumulated_profit", self._load_profit_from_csv())
        self._partial_sold_levels = set(data.get("partial_sold_levels", []))

    def _load_profit_from_csv(self):
        if not os.path.exists(ARQUIVO_LOG_TRADES):
            return 0.0
        total = 0.0
        try:
            with open(ARQUIVO_LOG_TRADES, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    lucro_str = row.get('LUCRO_USD', '0')
                    if lucro_str:
                        total += float(lucro_str)
        except Exception:
            pass
        return total

# =============================================================================
# SPIKE DETECTOR (SIMPLIFICADO, SEM ALTERAÇÕES)
# =============================================================================

class SpikeDetector:
    def __init__(self, config: Dict, exchange, shared_state, state_lock):
        self.config = config
        self.exchange = exchange
        self.shared_state = shared_state
        self.state_lock = state_lock

        self.enabled = config.get("SPIKE_ENABLED", False)
        self.timeframe = config.get("SPIKE_TIMEFRAME", "1m")
        self.vol_mult = config.get("SPIKE_VOLUME_MULTIPLIER", 5.0)
        self.vol_lookback = config.get("SPIKE_VOLUME_LOOKBACK", 20)
        self.breakout_pct = config.get("SPIKE_BREAKOUT_PCT", 0.4) / 100.0
        self.high_lookback = config.get("SPIKE_HIGH_LOOKBACK", 20)
        self.tp_pct = config.get("SPIKE_TAKE_PROFIT_PCT", 6.0) / 100.0
        self.ts_pct = config.get("SPIKE_TRAILING_STOP_PCT", 1.2) / 100.0
        self.sl_pct = config.get("SPIKE_STOP_LOSS_PCT", 3.5) / 100.0
        self.max_slippage = config.get("SPIKE_MAX_SLIPPAGE_PCT", 1.5) / 100.0
        self.max_hold = config.get("SPIKE_MAX_HOLD_SECONDS", 300)
        self.confirm_candles = config.get("SPIKE_CONFIRMATION_CANDLES", 2)
        self.use_dca_safety_order = config.get("SPIKE_USE_DCA_SAFETY_ORDER", True)
        self.pause_dca = config.get("SPIKE_PAUSE_DCA_DURING_SPIKE", True)

        self.dca_engine = None
        self.position_active = False
        self.entry_price = 0.0
        self.entry_time = 0
        self.peak_price = 0.0
        self.trail_stop = 0.0
        self.take_profit_hit = False
        self.last_candle_time = 0
        self.volume_history = deque(maxlen=self.vol_lookback)
        self.high_history = deque(maxlen=self.high_lookback)

        self.spike_lock = threading.Lock()
        self.last_spike_time = 0
        self.spike_cooldown = 60

    def set_dca_engine(self, dca_engine):
        self.dca_engine = dca_engine

    def _get_spike_capital(self):
        if self.dca_engine:
            return self.dca_engine.base_cfg["capital_base"]
        return 10.0

    def update_indicators(self):
        if not self.enabled:
            return
        try:
            with exchange_lock:
                ohlcv = self.exchange.fetch_ohlcv(self.config["SYMBOL"], timeframe=self.timeframe,
                                                  limit=self.high_lookback + 2)
            if not ohlcv:
                return
            last = ohlcv[-1]
            self.last_candle_time = last[0]
            current_volume = last[5]
            current_high = last[2]
            current_close = last[4]
            self.volume_history.append(current_volume)
            self.high_history.append(current_high)

            if not self.position_active:
                self._check_spike(current_volume, current_high, current_close, ohlcv)
            if self.position_active:
                self._manage_exit(current_close, current_high, last[3], last[0])
        except Exception as e:
            logging.warning(f"SpikeDetector error: {e}")

    def _check_spike(self, current_volume, current_high, current_close, ohlcv):
        if len(self.volume_history) < self.vol_lookback:
            return
        lookback = max(2, self.vol_lookback)
        avg_volume = sum(list(self.volume_history)[:-1]) / (lookback - 1)
        if current_volume < avg_volume * self.vol_mult:
            return
        highs = [c[2] for c in ohlcv[-self.high_lookback-1:-1]]
        recent_high = max(highs) if highs else 0
        if current_high < recent_high * (1 + self.breakout_pct):
            return
        if self.confirm_candles > 1:
            for i in range(1, self.confirm_candles + 1):
                idx = -i
                if ohlcv[idx][5] < avg_volume * self.vol_mult * 0.8:
                    return
                if ohlcv[idx][4] < recent_high:
                    return
        logging.info(f"🔥 SPIKE DETECTADO! Volume: {current_volume:.0f}, High: {current_high}")
        self._execute_entry(current_close)

    def _execute_entry(self, price_at_detection):
        with engine_lock:
            with self.state_lock:
                if self.shared_state.get("operating_paused", False):
                    return
                dca_active = self.shared_state.get("em_operacao", False)
                dca_trailing = self.shared_state.get("trailing_ativo", False)

            if self.use_dca_safety_order and dca_active and self.dca_engine and self.dca_engine.position:
                if not dca_trailing:
                    self._add_safety_order_to_dca(price_at_detection)
                else:
                    logging.info("Spike ignorado: DCA já em trailing.")
            else:
                self._open_spike_position(price_at_detection)

    def _add_safety_order_to_dca(self, price):
        with self.spike_lock:
            if self.position_active:
                return
        with engine_lock:
            if not self.dca_engine or not self.dca_engine.position:
                return
            params = self.dca_engine._active_params()
            if self.dca_engine.position["soUsed"] >= params["max_safety_orders"]:
                return
            cost = self._get_spike_capital()
            if self.dca_engine.cash < cost:
                return

            ordem = comprar_com_vault(cost, motivo=f"Spike SO #{self.dca_engine.position['soUsed']+1}")
            if not ordem['ok']:
                return
            qty = ordem['v']
            custo_real = ordem['c']
            preco_real = ordem['p']

            self.dca_engine.cash -= custo_real
            self.dca_engine.position["entries"].append({
                "price": preco_real, "qty": qty, "cost": custo_real, "time": int(time.time()*1000)
            })
            self.dca_engine.position["totalQty"] += qty
            self.dca_engine.position["totalCost"] += custo_real
            self.dca_engine.position["avgCost"] = safe_div(self.dca_engine.position["totalCost"],
                                                           self.dca_engine.position["totalQty"])
            self.dca_engine.position["soUsed"] += 1

            self.position_active = True
            self.entry_price = self.dca_engine.position["avgCost"]
            self.entry_time = time.time()
            self.peak_price = self.dca_engine.position["maxPrice"]
            self.trail_stop = self.peak_price * (1 - self.ts_pct)
            self.take_profit_hit = False

            with self.state_lock:
                self.shared_state["spike_controls_exit"] = True
        salvar_estado_disco()
        logging.info(f"✅ Spike assumiu controle da posição DCA+SO. Preço médio: {self.entry_price:.8f}")

    def _open_spike_position(self, price_at_detection):
        with self.spike_lock:
            if self.position_active:
                return
            now = time.time()
            if now - self.last_spike_time < self.spike_cooldown:
                return
            self.last_spike_time = now

        with self.state_lock:
            self.shared_state["spike_active"] = True

        try:
            with engine_lock:
                if self.dca_engine and self.dca_engine.position:
                    with self.state_lock:
                        self.shared_state["spike_active"] = False
                    return

                moeda = self.config["MOEDA_BASE"]
                symbol = self.config["SYMBOL"]
                capital_necessario = self._get_spike_capital()

                with exchange_lock:
                    bal_funding = self.exchange.fetch_balance({'type': 'funding'})
                    saldo_funding = bal_funding.get(moeda, {}).get('free', 0)
                if saldo_funding < capital_necessario:
                    with self.state_lock:
                        self.shared_state["spike_active"] = False
                    return

                if not transferir_para_spot(capital_necessario):
                    with self.state_lock:
                        self.shared_state["spike_active"] = False
                    return

                max_price = price_at_detection * (1 + self.max_slippage)
                with exchange_lock:
                    ordem = self.exchange.create_order(
                        symbol, 'market', 'buy', None,
                        params={'quoteOrderQty': capital_necessario}
                    )
                    preco_exec = float(ordem.get('average') or ordem.get('price') or 0)
                if preco_exec > max_price:
                    qtd = float(ordem['amount'])
                    with exchange_lock:
                        self.exchange.create_order(symbol, 'market', 'sell', qtd)
                    logging.warning(f"Slippage excessivo ({preco_exec:.8f} > {max_price:.8f}). Operação abortada.")
                    recolher_para_fundos()
                    with self.state_lock:
                        self.shared_state["spike_active"] = False
                    return

                self.position_active = True
                self.entry_price = preco_exec
                self.entry_time = time.time()
                self.peak_price = preco_exec
                self.take_profit_hit = False
                self.trail_stop = preco_exec * (1 - self.ts_pct)

                if self.dca_engine:
                    self.dca_engine.cash -= float(ordem['cost'])
                    with self.state_lock:
                        self.shared_state["cash"] = self.dca_engine.cash

                obs = f"Spike | price_at_detection={price_at_detection:.6f} | vol_mult={self.vol_mult} | breakout_pct={self.breakout_pct*100:.1f}%"
                Auditoria.log_transacao("COMPRA", preco_exec, float(ordem['amount']),
                                        float(ordem['cost']), obs=obs)
                logging.info(f"✅ Posição SPIKE aberta a {preco_exec:.8f}")
                salvar_estado_disco()
        except Exception as e:
            logging.error(f"Erro na compra do spike: {e}")
            with self.state_lock:
                self.shared_state["spike_active"] = False
            recolher_para_fundos()

    def _manage_exit(self, current_close, current_high, current_low, timestamp):
        if not self.position_active:
            return
        if current_high > self.peak_price:
            self.peak_price = current_high
            self.trail_stop = self.peak_price * (1 - self.ts_pct)
        profit_pct = safe_div(current_close - self.entry_price, self.entry_price)

        if self.tp_pct > 0 and not self.take_profit_hit and profit_pct >= self.tp_pct:
            self.take_profit_hit = True
            if self.ts_pct == 0:
                self._sell(current_close, "TAKE_PROFIT")
                return
        if self.ts_pct > 0 and (self.take_profit_hit or profit_pct > 0.01):
            if current_low <= self.trail_stop:
                self._sell(self.trail_stop, "TRAILING_STOP")
                return
        if self.sl_pct > 0 and profit_pct <= -self.sl_pct:
            self._sell(current_close, "STOP_LOSS")
            return
        if self.max_hold > 0 and (time.time() - self.entry_time) > self.max_hold:
            self._sell(current_close, "TIMEOUT")

    def _sell(self, price, reason):
        if not self.position_active:
            return
        with engine_lock:
            if self.dca_engine and self.dca_engine.position:
                qtd = self.dca_engine.position["totalQty"]
                custo = self.dca_engine.position["totalCost"]
                res = vender_quantidade(self.exchange, qtd, custo, f"SPIKE_{reason}",
                                        self.config, self.shared_state, self.state_lock, self.dca_engine.cash)
                if not res['ok']:
                    logging.error(f"Falha na venda unificada: {res.get('msg')}")
                    return
                self.dca_engine.cash += res['receita']
                recolher_para_fundos()
                Auditoria.log_transacao("VENDA", res['preco'], qtd,
                                        res['receita'], res['pnl'], res['pnl_pct'], self.dca_engine.cash,
                                        f"SPIKE_VENDA_UNIFICADA_{reason}")
                self.dca_engine.position = None
                self.dca_engine.cooldown = self.dca_engine.config["ENTRY_COOLDOWN"]
                with self.state_lock:
                    self.shared_state["em_operacao"] = False
                    self.shared_state["trailing_ativo"] = False
                    self.shared_state["max_p_trailing"] = 0.0
                salvar_estado_disco()
            else:
                base_currency = self.config["SYMBOL"].split('/')[0]
                with exchange_lock:
                    bal = self.exchange.fetch_balance()
                    qtd = bal[base_currency]['free']
                if qtd <= 0:
                    self.position_active = False
                    return
                with exchange_lock:
                    ordem = self.exchange.create_order(self.config["SYMBOL"], 'market', 'sell', qtd)
                    preco = float(ordem.get('average') or ordem.get('price') or 0)
                    receita = float(ordem.get('cost') or 0)
                custo = self._get_spike_capital()
                pnl = receita - custo
                pnl_pct = safe_div(pnl, custo) * 100
                profit_pct = safe_div(price - self.entry_price, self.entry_price) * 100
                obs = f"SPIKE_VENDA_{reason} | profit={profit_pct:.2f}% | peak={self.peak_price:.6f}"
                Auditoria.log_transacao("VENDA", preco, qtd, receita, pnl, pnl_pct, obs=obs)
                if self.dca_engine:
                    self.dca_engine.cash += receita
                    with self.state_lock:
                        self.shared_state["cash"] = self.dca_engine.cash
                recolher_para_fundos()
            with self.state_lock:
                self.shared_state["spike_controls_exit"] = False
                self.shared_state["spike_active"] = False
        self.position_active = False
        self.entry_price = 0
        self.peak_price = 0
        self.trail_stop = 0
        salvar_estado_disco()

    def to_dict(self):
        return {
            "position_active": self.position_active,
            "entry_price": self.entry_price,
            "entry_time": self.entry_time,
            "peak_price": self.peak_price,
            "trail_stop": self.trail_stop,
            "take_profit_hit": self.take_profit_hit,
            "last_spike_time": self.last_spike_time,
            "last_candle_time": self.last_candle_time,
        }

    def from_dict(self, data):
        self.position_active = data.get("position_active", False)
        self.entry_price = data.get("entry_price", 0.0)
        self.entry_time = data.get("entry_time", 0)
        self.peak_price = data.get("peak_price", 0.0)
        self.trail_stop = data.get("trail_stop", 0.0)
        self.take_profit_hit = data.get("take_profit_hit", False)

# =============================================================================
# SISTEMA DE AUDITORIA
# =============================================================================

class Auditoria:
    @staticmethod
    def configurar():
        root_logger = logging.getLogger()
        if not root_logger.handlers:
            with config_lock:
                max_bytes    = CONFIG.get("LOG_MAX_BYTES",    5_242_880)
                backup_count = CONFIG.get("LOG_BACKUP_COUNT", 5)
            handler = logging.handlers.RotatingFileHandler(
                ARQUIVO_LOG_SISTEMA,
                maxBytes    = max_bytes,
                backupCount = backup_count,
                encoding    = "utf-8",
            )
            handler.setFormatter(logging.Formatter(
                "%(asctime)s - %(levelname)s - %(message)s",
                datefmt="%Y-%m-%d %H:%M:%S",
            ))
            root_logger.setLevel(logging.INFO)
            root_logger.addHandler(handler)
        if not os.path.exists(ARQUIVO_LOG_TRADES):
            with open(ARQUIVO_LOG_TRADES, 'w', newline='', encoding='utf-8') as f:
                csv.writer(f).writerow([
                    "DATA", "PAR", "TIPO", "PRECO", "QTD",
                    "TOTAL_USD", "LUCRO_USD", "LUCRO_PERC", "SALDO_VAULT", "OBS"
                ])

    @staticmethod
    def log_sistema(msg, nivel="INFO"):
        nivel = {"INFO": "info", "AVISO": "warning", "ERRO": "error", "CRITICO": "critical"}.get(nivel, "info")
        getattr(logging, nivel)(msg)
        return msg

    @staticmethod
    def log_transacao(tipo, preco, qtd, total_usd, lucro_usd=0.0, lucro_perc=0.0, saldo_vault=0.0, obs=""):
        with config_lock:
            symbol = CONFIG["SYMBOL"]
        linha = [
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            symbol, tipo,
            f"{preco:.8f}", f"{qtd:.8f}", f"{total_usd:.2f}",
            f"{lucro_usd:.2f}", f"{lucro_perc:.2f}%",
            f"{saldo_vault:.2f}", obs
        ]
        logging.info(f"LOG_TRANSACAO: {linha}")
        with csv_lock:
            with open(ARQUIVO_LOG_TRADES, 'a', newline='', encoding='utf-8') as f:
                csv.writer(f).writerow(linha)

# =============================================================================
# VERIFICAÇÕES GERAIS
# =============================================================================

exchange_failures = 0

def verificar_conexao() -> bool:
    global exchange_failures
    try:
        with exchange_lock:
            exchange.fetch_time()
        exchange_failures = 0
        with state_lock:
            if not shared_state["conn_ok"]:
                logging.info("Conexão restaurada.")
                shared_state["conn_ok"] = True
                shared_state["conn_error_msg"] = ""
        return True
    except Exception as e:
        with state_lock:
            if shared_state["conn_ok"]:
                logging.error(f"Conexão perdida: {e}.")
                shared_state["conn_ok"] = False
                shared_state["conn_error_msg"] = str(e)
            else:
                if exchange_failures % 10 == 0:
                    logging.warning(f"Conexão ainda indisponível ({exchange_failures} falhas)")
        exchange_failures += 1
        return False

def is_paused_time() -> bool:
    if not CONFIG.get("OPERATING_HOURS_ENABLED", True):
        return False
    now = datetime.now()
    current_weekday = now.weekday()
    current_minutes = current_weekday * 1440 + now.hour * 60 + now.minute
    day_map = {"monday":0,"tuesday":1,"wednesday":2,"thursday":3,"friday":4,"saturday":5,"sunday":6}
    start_day = day_map[CONFIG["OPERATING_START_DAY"]]
    end_day = day_map[CONFIG["OPERATING_END_DAY"]]
    start_h, start_m = map(int, CONFIG["OPERATING_START_TIME"].split(':'))
    end_h, end_m = map(int, CONFIG["OPERATING_END_TIME"].split(':'))
    start_minutes = start_day * 1440 + start_h * 60 + start_m
    end_minutes = end_day * 1440 + end_h * 60 + end_m
    if start_minutes <= end_minutes:
        return start_minutes <= current_minutes <= end_minutes
    else:
        return current_minutes >= start_minutes or current_minutes <= end_minutes

# =============================================================================
# ESTADO COMPARTILHADO
# =============================================================================

shared_state = {
    "filtros": {"MTF": "?"},
    "preco": 0.0,
    "erros_consecutivos": 0,
    "marcha": "INICIALIZANDO...",
    "em_operacao": False,
    "preco_medio": 0.0,
    "lucro_perc_atual": 0.0,
    "perda_usd_atual": 0.0,
    "proxima_compra_p": 0.0,
    "num_safety_orders": 0,
    "alvo_trailing_ativacao": 0.0,
    "stop_atual_trailing": 0.0,
    "trailing_ativo": False,
    "max_p_trailing": 0.0,
    "circuit_breaker": False,
    "rsi_atual": 0.0,
    "volume_ok": False,
    "current_regime": "STANDBY",
    "cash": 0.0,
    "msg_log": "Sistema Iniciado",
    "spike_controls_exit": False,
    "spike_active": False,
    "high_intrabar": 0.0,
    "high_intrabar_timestamp": 0,
    "conn_ok": True,
    "conn_error_msg": "",
    "operating_paused": False,
}

menu_ativo = False
exchange = None
dca_engine: Optional[DCAEngineBacktest] = None
spike_detector: Optional[SpikeDetector] = None

# =============================================================================
# CONFIGURAÇÃO PADRÃO (SIMPLIFICADA + RANGE MODE)
# =============================================================================

CONFIG = {
    "API_KEY": "", "SECRET": "",
    "SYMBOL": "BTC/USDT", "MOEDA_BASE": "USDT",
    "CAPITAL_TOTAL": 20.0, "CAPITAL_BASE": 10.0,
    "MAX_SAFETY_ORDERS": 1,
    "DCA_VOLUME_SCALE": 1.0, "DCA_STEP_INITIAL": 0.012, "DCA_STEP_SCALE": 1.2,
    "TRAILING_TRIGGER": 0.010, "TRAILING_DIST": 0.006, "STOP_LOSS": 0.030,
    "COMPOUND": False,
    "ENTRY_COOLDOWN": 2,
    "RSI_MAX_ENTRADA": 65.0, "RSI_PERIOD": 14,
    "VOLUME_FATOR_MIN": 1.2,
    "ATR_PERIOD": 14, "TIMEFRAME": "5m",
    "REGIME_SAFE_MODE": True,
    "LOG_MAX_BYTES": 5_242_880, "LOG_BACKUP_COUNT": 5,
    "TAKE_PROFIT_LEVELS": [2.0, 3.5], "TAKE_PROFIT_SIZES": [0.4, 0.6],
    "MAX_HOLD_HOURS": 0,
    "ENTRY_SCORE_THRESHOLD": 0.75,
    "CHANDELIER_ENABLED": True, "CHANDELIER_FACTOR": 3.0,
    "STAGNATION_EXIT": True, "MAX_CANDLES_NO_HIGH": 45, "MIN_PROFIT_PCT": 0.008,
    "EMA_CROSS_EXIT": True, "MIN_PROFIT_PCT_EMA": 0.008,
    "VOLUME_DUMP_EXIT": True, "VOLUME_DUMP_MULTIPLIER": 3.5,
    "VOLUME_DUMP_DROP_PCT": 0.6, "VOLUME_DUMP_CONFIRM_CANDLES": 2,
    "EXIT_SCORE_THRESHOLD": 8.5,
    # Spike
    "SPIKE_ENABLED": True,
    "SPIKE_TIMEFRAME": "1m",
    "SPIKE_VOLUME_MULTIPLIER": 5.0,
    "SPIKE_VOLUME_LOOKBACK": 20,
    "SPIKE_BREAKOUT_PCT": 0.4,
    "SPIKE_HIGH_LOOKBACK": 20,
    "SPIKE_TAKE_PROFIT_PCT": 6.0,
    "SPIKE_TRAILING_STOP_PCT": 1.2,
    "SPIKE_STOP_LOSS_PCT": 3.5,
    "SPIKE_MAX_SLIPPAGE_PCT": 1.5,
    "SPIKE_MAX_HOLD_SECONDS": 300,
    "SPIKE_CONFIRMATION_CANDLES": 2,
    "SPIKE_USE_DCA_SAFETY_ORDER": True,
    "SPIKE_PAUSE_DCA_DURING_SPIKE": True,
    # Range Trading Mode
    "RANGE_MODE_ENABLED": False,
    "RANGE_ADX_THRESHOLD": 20,
    "RANGE_BB_PERIOD": 20,
    "RANGE_BB_STD": 2.0,
    "RANGE_RSI_OVERSOLD": 35,
    "RANGE_RSI_OVERBOUGHT": 65,
    "RANGE_TAKE_PROFIT_PCT": 0.01,
    "RANGE_STOP_LOSS_PCT": 0.005,
    "RANGE_USE_BAND_EXIT": True,
    # Horário
    "OPERATING_HOURS_ENABLED": True,
    "OPERATING_START_DAY": "saturday",
    "OPERATING_START_TIME": "00:00",
    "OPERATING_END_DAY": "sunday",
    "OPERATING_END_TIME": "00:00",
}

# =============================================================================
# PERSISTÊNCIA
# =============================================================================

STATE_SCHEMA_VERSION = 11   # atualizado devido às correções de estado

def salvar_estado_disco():
    try:
        with engine_lock, state_lock:
            estado_motor = dca_engine.to_dict() if dca_engine else {}
            dados = {
                "schema_version": STATE_SCHEMA_VERSION,
                "em_operacao": shared_state["em_operacao"],
                "symbol": CONFIG["SYMBOL"],
                "max_p_trailing": shared_state["max_p_trailing"],
                "trailing_ativo": shared_state["trailing_ativo"],
                "motor": estado_motor,
                "timestamp": str(datetime.now()),
                "high_intrabar": shared_state.get("high_intrabar", 0.0),
                "high_intrabar_timestamp": shared_state.get("high_intrabar_timestamp", 0),
                "spike_controls_exit": shared_state.get("spike_controls_exit", False),
                "spike_active": shared_state.get("spike_active", False),
            }
            if spike_detector:
                dados["spike_detector"] = spike_detector.to_dict()
                dados["spike_volume_history"] = list(spike_detector.volume_history)
                dados["spike_high_history"] = list(spike_detector.high_history)
        with open(ARQUIVO_ESTADO, "w") as f:
            json.dump(dados, f, indent=4)
    except Exception as e:
        logging.error(f"Erro ao salvar estado: {e}")

def carregar_estado_disco():
    if not os.path.exists(ARQUIVO_ESTADO):
        return False
    try:
        with open(ARQUIVO_ESTADO) as f:
            dados = json.load(f)
        if dados.get("em_operacao") and dados.get("symbol") == CONFIG["SYMBOL"]:
            with state_lock:
                shared_state["em_operacao"] = True
                shared_state["marcha"] = "RECUPERANDO..."
                shared_state["max_p_trailing"] = dados.get("max_p_trailing", 0.0)
                shared_state["trailing_ativo"] = dados.get("trailing_ativo", False)
                shared_state["high_intrabar"] = dados.get("high_intrabar", 0.0)
                shared_state["high_intrabar_timestamp"] = dados.get("high_intrabar_timestamp", 0)
                shared_state["spike_controls_exit"] = dados.get("spike_controls_exit", False)
                shared_state["spike_active"] = dados.get("spike_active", False)

            if dca_engine and "motor" in dados:
                with engine_lock:
                    dca_engine.from_dict(dados["motor"])
                if dca_engine.position and (dca_engine.position["totalCost"] <= 0 or dca_engine.position["totalQty"] <= 0):
                    logging.error("Estado restaurado com posição inválida. Resetando.")
                    dca_engine.position = None
                    dca_engine.cash = CONFIG["CAPITAL_TOTAL"]
                    with state_lock:
                        shared_state["em_operacao"] = False
                    salvar_estado_disco()
                if dca_engine.position:
                    state = dca_engine.get_state()
                    with state_lock:
                        shared_state.update(state)
                        shared_state["cash"] = dca_engine.cash
                        shared_state["em_operacao"] = True
                        shared_state["marcha"] = "DCA ATIVO (REC)"
                else:
                    with state_lock:
                        shared_state["cash"] = dca_engine.cash

            if spike_detector and "spike_detector" in dados:
                spike_detector.from_dict(dados["spike_detector"])
                if "spike_volume_history" in dados:
                    spike_detector.volume_history = deque(dados["spike_volume_history"],
                                                           maxlen=spike_detector.vol_lookback)
                if "spike_high_history" in dados:
                    spike_detector.high_history = deque(dados["spike_high_history"],
                                                        maxlen=spike_detector.high_lookback)
                spike_detector.last_spike_time = dados.get("spike_last_spike_time", 0)
                spike_detector.last_candle_time = dados.get("spike_last_candle_time", 0)

            try:
                ticker = exchange.fetch_ticker(CONFIG["SYMBOL"])
                current_price = ticker['last']
                with state_lock:
                    shared_state["preco"] = current_price
                    if shared_state.get("em_operacao") and current_price > shared_state["high_intrabar"]:
                        shared_state["high_intrabar"] = current_price
                        shared_state["high_intrabar_timestamp"] = int(time.time() * 1000)
            except Exception as e:
                logging.warning(f"Erro ao buscar preço via REST: {e}")
            return True
    except Exception as e:
        Auditoria.log_sistema(f"Erro ao ler save: {e}", "ERRO")
    return False

# =============================================================================
# FUNÇÕES DE CONEXÃO E ORDENS
# =============================================================================

def definir_status(msg, tipo="INFO"):
    hora = datetime.now().strftime("%H:%M:%S")
    cor  = {"SUCESSO": Fore.GREEN, "ERRO": Fore.RED, "AVISO": Fore.YELLOW}.get(tipo, Fore.CYAN)
    with state_lock:
        shared_state["msg_log"] = f"{Fore.WHITE}[{hora}] {cor}{msg}"
    if tipo == "ERRO":      Auditoria.log_sistema(msg, "ERRO")
    elif tipo == "SUCESSO": Auditoria.log_sistema(msg, "INFO")

def panico_sistema(mensagem):
    logging.critical(f"DISJUNTOR ATIVADO: {mensagem}")
    definir_status(f"ERRO CRÍTICO: {mensagem} — DESLIGANDO", "ERRO")
    salvar_estado_disco()
    sys.exit(1)

def get_saldo_fundos() -> float:
    with config_lock:
        moeda = CONFIG["MOEDA_BASE"]
    try:
        with exchange_lock:
            bal = exchange.fetch_balance({'type': 'funding'})
            return bal.get(moeda, {}).get('free', 0)
    except Exception:
        return 0

def transferir_para_spot(valor: float) -> bool:
    with config_lock:
        moeda = CONFIG["MOEDA_BASE"]
    try:
        with exchange_lock:
            exchange.transfer(moeda, valor, 'funding', 'spot')
        Auditoria.log_sistema(f"VAULT: ${valor:.2f} enviado ao Spot", "INFO")
        time.sleep(1)
        return True
    except Exception as e:
        definir_status(f"Erro Vault (Fundos→Spot): {e}", "ERRO")
        return False

def recolher_para_fundos() -> bool:
    with config_lock:
        moeda = CONFIG["MOEDA_BASE"]
    try:
        with exchange_lock:
            balance = exchange.fetch_balance()
            saldo_usdt = balance.get(moeda, {}).get('free', 0)
        if saldo_usdt > 0.5:
            with exchange_lock:
                exchange.transfer(moeda, saldo_usdt, 'spot', 'funding')
            Auditoria.log_sistema(f"VAULT: ${saldo_usdt:.2f} protegido em Fundos", "INFO")
        return True
    except Exception as e:
        definir_status(f"Erro Vault (Spot→Fundos): {e}", "ERRO")
        return False

def comprar_com_vault(valor_usd: float, motivo: str = "Entrada") -> dict:
    with config_lock:
        moeda = CONFIG["MOEDA_BASE"]
    try:
        with exchange_lock:
            bal_funding = exchange.fetch_balance({'type': 'funding'})
            saldo_usdt_funding = bal_funding.get(moeda, {}).get('free', 0)
        if saldo_usdt_funding < valor_usd:
            logging.error(f"Saldo insuficiente no Funding: {saldo_usdt_funding:.2f} < {valor_usd:.2f}")
            return {'ok': False, 'msg': f'Saldo Funding insuficiente'}
    except Exception as e:
        logging.error(f"Erro ao verificar saldo Funding: {e}")
        return {'ok': False, 'msg': str(e)}

    if not transferir_para_spot(valor_usd):
        return {'ok': False, 'msg': 'Falha na transferência Fundos→Spot'}
    with config_lock:
        symbol = CONFIG['SYMBOL']
    try:
        with exchange_lock:
            ordem = exchange.create_order(
                symbol, 'market', 'buy', None,
                params={'quoteOrderQty': exchange.cost_to_precision(symbol, valor_usd)}
            )
        with state_lock:
            shared_state["erros_consecutivos"] = 0
        preco_exec = float(ordem.get('average') or ordem.get('price') or 0)
        res = {'ok': True, 'p': preco_exec,
               'v': float(ordem['amount']), 'c': float(ordem['cost'])}
        Auditoria.log_transacao("COMPRA", res['p'], res['v'], res['c'], obs=motivo)
        return res
    except Exception as e:
        with state_lock:
            shared_state["erros_consecutivos"] += 1
            cnt = shared_state["erros_consecutivos"]
        logging.error(f"Erro Compra: {e} ({cnt}/5)")
        definir_status("Ordem falhou! Recolhendo ao Vault...", "AVISO")
        recolher_para_fundos()
        return {'ok': False, 'msg': str(e)}

def inicializar_vault():
    definir_status("Auditando Vault...", "INFO")
    recolher_para_fundos()
    try:
        saldo = get_saldo_fundos()
        nivel = "AVISO" if saldo < 120 else "SUCESSO"
        definir_status(f"Vault: ${saldo:.2f}", nivel)
    except Exception as e:
        definir_status(f"Erro Vault Init: {e}", "ERRO")

def validate_config() -> None:
    errs = []
    if CONFIG["DCA_STEP_INITIAL"] <= 0:
        errs.append("DCA_STEP_INITIAL > 0")
    if CONFIG["DCA_STEP_SCALE"] <= 0:
        errs.append("DCA_STEP_SCALE > 0")
    if not (0 < CONFIG["TRAILING_DIST"] < 1):
        errs.append("TRAILING_DIST entre 0 e 1")
    if not (0 <= CONFIG["TRAILING_TRIGGER"] < 1):
        errs.append("TRAILING_TRIGGER entre 0 e 1")
    if CONFIG["MAX_SAFETY_ORDERS"] < 0:
        errs.append("MAX_SAFETY_ORDERS >= 0")
    tp_levels = CONFIG.get("TAKE_PROFIT_LEVELS", [])
    tp_sizes = CONFIG.get("TAKE_PROFIT_SIZES", [])
    if len(tp_levels) != len(tp_sizes):
        errs.append("TAKE_PROFIT_LEVELS e TAKE_PROFIT_SIZES devem ter o mesmo tamanho")
    if tp_sizes and sum(tp_sizes) > 1.0:
        errs.append("Soma de TAKE_PROFIT_SIZES não pode exceder 1.0")
    if errs:
        for e in errs:
            logging.error(f"Config inválida: {e}")
        raise ValueError("Configuração inválida. Corrija config.ini antes de iniciar.")

# =============================================================================
# CARREGAR CONFIGURAÇÕES
# =============================================================================

def carregar_configuracoes():
    global exchange, CONFIG, dca_engine, spike_detector
    if not os.path.exists("config.ini"):
        Auditoria.log_sistema("Arquivo config.ini não encontrado. Usando configurações padrão.", "AVISO")
    else:
        cp = configparser.ConfigParser(inline_comment_prefixes=("#", ";"))
        cp.read("config.ini")
        CONFIG["API_KEY"] = cp.get("binance", "api_key", fallback=CONFIG["API_KEY"])
        CONFIG["SECRET"]  = cp.get("binance", "secret", fallback=CONFIG["SECRET"])
        if "mercado" in cp:
            mg = cp["mercado"]
            CONFIG["SYMBOL"]      = mg.get("symbol", CONFIG["SYMBOL"])
            CONFIG["MOEDA_BASE"]  = CONFIG["SYMBOL"].split('/')[1] if '/' in CONFIG["SYMBOL"] else "USDT"
            CONFIG["CAPITAL_TOTAL"] = float(mg.get("capital_total", CONFIG["CAPITAL_TOTAL"]))
            CONFIG["CAPITAL_BASE"]  = float(mg.get("capital_base", CONFIG["CAPITAL_BASE"]))
            CONFIG["COMPOUND"]      = mg.getboolean("compound", CONFIG["COMPOUND"])
        if "trading" in cp:
            tg = cp["trading"]
            CONFIG["MAX_SAFETY_ORDERS"] = int(tg.get("max_safety_orders", CONFIG["MAX_SAFETY_ORDERS"]))
            CONFIG["DCA_VOLUME_SCALE"]  = float(tg.get("dca_volume_scale", CONFIG["DCA_VOLUME_SCALE"]))
            CONFIG["DCA_STEP_INITIAL"]  = float(tg.get("dca_step_initial", CONFIG["DCA_STEP_INITIAL"]))
            CONFIG["DCA_STEP_SCALE"]    = float(tg.get("dca_step_scale", CONFIG["DCA_STEP_SCALE"]))
            CONFIG["TRAILING_TRIGGER"]  = float(tg.get("trailing_trigger", CONFIG["TRAILING_TRIGGER"]))
            CONFIG["TRAILING_DIST"]     = float(tg.get("trailing_dist", CONFIG["TRAILING_DIST"]))
            CONFIG["STOP_LOSS"]         = float(tg.get("stop_loss", CONFIG["STOP_LOSS"]))
            CONFIG["RSI_MAX_ENTRADA"]   = float(tg.get("rsi_max_entrada", CONFIG["RSI_MAX_ENTRADA"]))
            CONFIG["RSI_PERIOD"]        = int(tg.get("rsi_period", CONFIG["RSI_PERIOD"]))
            CONFIG["VOLUME_FATOR_MIN"]  = float(tg.get("volume_fator_min", CONFIG["VOLUME_FATOR_MIN"]))
            CONFIG["ATR_PERIOD"]        = int(tg.get("atr_period", CONFIG["ATR_PERIOD"]))
            CONFIG["TIMEFRAME"]         = tg.get("timeframe", CONFIG["TIMEFRAME"])
            CONFIG["ENTRY_SCORE_THRESHOLD"] = float(tg.get("entry_score_threshold", CONFIG["ENTRY_SCORE_THRESHOLD"]))
            CONFIG["CHANDELIER_ENABLED"] = tg.getboolean("chandelier_enabled", CONFIG["CHANDELIER_ENABLED"])
            CONFIG["CHANDELIER_FACTOR"] = float(tg.get("chandelier_factor", CONFIG["CHANDELIER_FACTOR"]))
            CONFIG["EXIT_SCORE_THRESHOLD"] = float(tg.get("exit_score_threshold", CONFIG["EXIT_SCORE_THRESHOLD"]))
            CONFIG["TAKE_PROFIT_LEVELS"] = [float(x.strip()) for x in tg.get("take_profit_levels", "").split(",")] if tg.get("take_profit_levels") else []
            CONFIG["TAKE_PROFIT_SIZES"] = [float(x.strip()) for x in tg.get("take_profit_sizes", "").split(",")] if tg.get("take_profit_sizes") else []
            # Range mode
            CONFIG["RANGE_MODE_ENABLED"] = tg.getboolean("range_mode_enabled", CONFIG["RANGE_MODE_ENABLED"])
            CONFIG["RANGE_ADX_THRESHOLD"] = float(tg.get("range_adx_threshold", CONFIG["RANGE_ADX_THRESHOLD"]))
            CONFIG["RANGE_BB_PERIOD"] = int(tg.get("range_bb_period", CONFIG["RANGE_BB_PERIOD"]))
            CONFIG["RANGE_BB_STD"] = float(tg.get("range_bb_std", CONFIG["RANGE_BB_STD"]))
            CONFIG["RANGE_RSI_OVERSOLD"] = float(tg.get("range_rsi_oversold", CONFIG["RANGE_RSI_OVERSOLD"]))
            CONFIG["RANGE_RSI_OVERBOUGHT"] = float(tg.get("range_rsi_overbought", CONFIG["RANGE_RSI_OVERBOUGHT"]))
            CONFIG["RANGE_TAKE_PROFIT_PCT"] = float(tg.get("range_take_profit_pct", CONFIG["RANGE_TAKE_PROFIT_PCT"]))
            CONFIG["RANGE_STOP_LOSS_PCT"] = float(tg.get("range_stop_loss_pct", CONFIG["RANGE_STOP_LOSS_PCT"]))
            CONFIG["RANGE_USE_BAND_EXIT"] = tg.getboolean("range_use_band_exit", CONFIG["RANGE_USE_BAND_EXIT"])
        if "regime" in cp:
            rg = cp["regime"]
            CONFIG["REGIME_SAFE_MODE"] = rg.getboolean("regime_safe_mode", CONFIG["REGIME_SAFE_MODE"])
        if "exit_advanced" in cp:
            ea = cp["exit_advanced"]
            CONFIG["STAGNATION_EXIT"]      = ea.getboolean("stagnation_exit", CONFIG["STAGNATION_EXIT"])
            CONFIG["MAX_CANDLES_NO_HIGH"]  = int(ea.get("max_candles_no_high", CONFIG["MAX_CANDLES_NO_HIGH"]))
            CONFIG["MIN_PROFIT_PCT"]       = float(ea.get("min_profit_pct", CONFIG["MIN_PROFIT_PCT"]))
            CONFIG["EMA_CROSS_EXIT"]       = ea.getboolean("ema_cross_exit", CONFIG["EMA_CROSS_EXIT"])
            CONFIG["MIN_PROFIT_PCT_EMA"]   = float(ea.get("min_profit_pct_ema", CONFIG["MIN_PROFIT_PCT_EMA"]))
            CONFIG["VOLUME_DUMP_EXIT"]     = ea.getboolean("volume_dump_exit", CONFIG["VOLUME_DUMP_EXIT"])
            CONFIG["VOLUME_DUMP_MULTIPLIER"] = float(ea.get("volume_dump_multiplier", CONFIG["VOLUME_DUMP_MULTIPLIER"]))
            CONFIG["VOLUME_DUMP_CONFIRM_CANDLES"] = int(ea.get("volume_dump_confirm_candles", CONFIG["VOLUME_DUMP_CONFIRM_CANDLES"]))
            CONFIG["VOLUME_DUMP_DROP_PCT"] = float(ea.get("volume_dump_drop_pct", CONFIG["VOLUME_DUMP_DROP_PCT"]))
        if "spike" in cp:
            sp = cp["spike"]
            CONFIG["SPIKE_ENABLED"] = sp.getboolean("enabled", CONFIG["SPIKE_ENABLED"])
            CONFIG["SPIKE_TIMEFRAME"] = sp.get("timeframe", CONFIG["SPIKE_TIMEFRAME"])
            CONFIG["SPIKE_VOLUME_MULTIPLIER"] = float(sp.get("volume_multiplier", CONFIG["SPIKE_VOLUME_MULTIPLIER"]))
            CONFIG["SPIKE_VOLUME_LOOKBACK"] = int(sp.get("volume_lookback", CONFIG["SPIKE_VOLUME_LOOKBACK"]))
            CONFIG["SPIKE_BREAKOUT_PCT"] = float(sp.get("breakout_pct", CONFIG["SPIKE_BREAKOUT_PCT"]))
            CONFIG["SPIKE_HIGH_LOOKBACK"] = int(sp.get("high_lookback", CONFIG["SPIKE_HIGH_LOOKBACK"]))
            CONFIG["SPIKE_TAKE_PROFIT_PCT"] = float(sp.get("take_profit_pct", CONFIG["SPIKE_TAKE_PROFIT_PCT"]))
            CONFIG["SPIKE_TRAILING_STOP_PCT"] = float(sp.get("trailing_stop_pct", CONFIG["SPIKE_TRAILING_STOP_PCT"]))
            CONFIG["SPIKE_STOP_LOSS_PCT"] = float(sp.get("stop_loss_pct", CONFIG["SPIKE_STOP_LOSS_PCT"]))
            CONFIG["SPIKE_MAX_SLIPPAGE_PCT"] = float(sp.get("max_slippage_pct", CONFIG["SPIKE_MAX_SLIPPAGE_PCT"]))
            CONFIG["SPIKE_MAX_HOLD_SECONDS"] = int(sp.get("max_hold_seconds", CONFIG["SPIKE_MAX_HOLD_SECONDS"]))
            CONFIG["SPIKE_CONFIRMATION_CANDLES"] = int(sp.get("confirmation_candles", CONFIG["SPIKE_CONFIRMATION_CANDLES"]))
            CONFIG["SPIKE_USE_DCA_SAFETY_ORDER"] = sp.getboolean("use_dca_safety_order", CONFIG["SPIKE_USE_DCA_SAFETY_ORDER"])
            CONFIG["SPIKE_PAUSE_DCA_DURING_SPIKE"] = sp.getboolean("pause_dca_during_spike", CONFIG["SPIKE_PAUSE_DCA_DURING_SPIKE"])
        if "operating_hours" in cp:
            oh = cp["operating_hours"]
            CONFIG["OPERATING_HOURS_ENABLED"] = oh.getboolean("enabled", CONFIG["OPERATING_HOURS_ENABLED"])
            CONFIG["OPERATING_START_DAY"] = oh.get("start_day", CONFIG["OPERATING_START_DAY"]).lower()
            CONFIG["OPERATING_START_TIME"] = oh.get("start_time", CONFIG["OPERATING_START_TIME"])
            CONFIG["OPERATING_END_DAY"] = oh.get("end_day", CONFIG["OPERATING_END_DAY"]).lower()
            CONFIG["OPERATING_END_TIME"] = oh.get("end_time", CONFIG["OPERATING_END_TIME"])
        if "logging" in cp:
            lg = cp["logging"]
            CONFIG["LOG_MAX_BYTES"] = int(lg.get("log_max_bytes", CONFIG["LOG_MAX_BYTES"]))
            CONFIG["LOG_BACKUP_COUNT"] = int(lg.get("log_backup_count", CONFIG["LOG_BACKUP_COUNT"]))

    validate_config()
    Auditoria.configurar()

    try:
        print(f"{Fore.CYAN}🔌 Conectando à Binance...{Fore.WHITE}")
        exchange = ccxt.binance({
            'apiKey': CONFIG["API_KEY"] or '',
            'secret': CONFIG["SECRET"] or '',
            'enableRateLimit': True,
            'options': {'adjustForTimeDifference': True},
        })
        with exchange_lock:
            exchange.load_markets()
        print(f"{Fore.GREEN}✅ Conectado!{Fore.WHITE}")
        definir_status(f"Conectado: {CONFIG['SYMBOL']}", "SUCESSO")
    except Exception as e:
        print(f"❌ Erro Crítico ao conectar: {e}")
        sys.exit(1)

    dca_engine = DCAEngineBacktest(dict(CONFIG), exchange, state_lock, shared_state)
    spike_detector = SpikeDetector(CONFIG, exchange, shared_state, state_lock)
    spike_detector.set_dca_engine(dca_engine)
    carregar_estado_disco()

    try:
        with exchange_lock:
            ohlcv = exchange.fetch_ohlcv(CONFIG["SYMBOL"], timeframe=CONFIG["TIMEFRAME"], limit=200)
        for k in ohlcv:
            dca_engine.price_history.append(k[4])
            dca_engine.price_history_high.append(k[2])
            dca_engine.price_history_low.append(k[3])
            dca_engine.volume_history.append(k[5])
            dca_engine.candles_history.append({
                'o': k[1], 'h': k[2], 'l': k[3], 'c': k[4], 'v': k[5], 't': k[0]
            })
        if len(dca_engine.candles_history) >= dca_engine.atr_period + 1:
            dca_engine._initialize_atr(list(dca_engine.candles_history))
        if len(dca_engine.price_history) >= 50:
            closes = list(dca_engine.price_history)
            rsi = compute_rsi(closes, CONFIG["RSI_PERIOD"])[-1]
            dca_engine.current_regime = compute_regime_simple(closes, rsi)
            with state_lock:
                shared_state["current_regime"] = dca_engine.current_regime
                shared_state["rsi_atual"] = rsi
    except Exception as e:
        logging.warning(f"Erro ao buscar dados históricos: {e}")

    if dca_engine and dca_engine.position:
        symbol = CONFIG["SYMBOL"]
        base_currency = symbol.split('/')[0]
        try:
            with exchange_lock:
                real_balance = exchange.fetch_balance()[base_currency]['free']
            if real_balance < dca_engine.position["totalQty"] * 0.9:
                logging.warning(f"Saldo real ({real_balance}) muito menor que o esperado. Resetando posição.")
                dca_engine.cash = CONFIG["CAPITAL_TOTAL"]
                dca_engine.position = None
                with state_lock:
                    shared_state["em_operacao"] = False
                salvar_estado_disco()
        except Exception as e:
            logging.warning(f"Erro ao reconciliar saldo: {e}")

# =============================================================================
# THREADS (SIMPLIFICADAS, MANTIDAS DA VERSÃO ANTERIOR)
# =============================================================================

def thread_scanner():
    while True:
        with state_lock:
            if not shared_state["conn_ok"]:
                time.sleep(5)
                continue
        try:
            with config_lock:
                symbol = CONFIG["SYMBOL"]
                cb_ativo = CONFIG.get("CIRCUIT_BREAKER_ATIVO", True)
                cb_queda = CONFIG.get("CB_QUEDA_PCT", 1.5)
                cb_janela = CONFIG.get("CB_JANELA_VELAS", 3)
                main_tf = CONFIG.get("TIMEFRAME", "5m")
            if cb_ativo:
                try:
                    with exchange_lock:
                        ohlcv = exchange.fetch_ohlcv(symbol, timeframe='4h', limit=cb_janela+2)
                    df = pd.DataFrame(ohlcv, columns=['t','o','h','l','c','v'])
                    preco_inicio = float(df['c'].iloc[-(cb_janela+1)])
                    preco_atual  = float(df['c'].iloc[-1])
                    variacao = (safe_div(preco_atual, preco_inicio) - 1) * 100
                    with state_lock:
                        shared_state["circuit_breaker"] = variacao <= -cb_queda
                except Exception as e:
                    logging.warning(f"Erro CB: {e}")
            try:
                with exchange_lock:
                    ohlcv = exchange.fetch_ohlcv(symbol, timeframe=main_tf, limit=50)
                df = pd.DataFrame(ohlcv, columns=['t','o','h','l','c','v'])
                closes = df['c'].astype(float).tolist()
                rsi = compute_rsi(closes, CONFIG["RSI_PERIOD"])[-1] if len(closes) > CONFIG["RSI_PERIOD"] else 50
                with state_lock:
                    shared_state["rsi_atual"] = rsi
                if CONFIG.get("FILTRO_VOLUME_ATIVO", True):
                    vol_atual = float(df['v'].iloc[-1])
                    vol_media = float(df['v'].rolling(20).mean().iloc[-1])
                    vol_ok = vol_atual >= vol_media * CONFIG["VOLUME_FATOR_MIN"] if not pd.isna(vol_media) else False
                    with state_lock:
                        shared_state["volume_ok"] = vol_ok
            except Exception as e:
                logging.warning(f"Erro indicadores: {e}")
            try:
                with exchange_lock:
                    ohlcv_mtf = exchange.fetch_ohlcv(symbol, timeframe=main_tf, limit=100)
                df_mtf = pd.DataFrame(ohlcv_mtf, columns=['t','o','h','l','c','v'])
                closes_mtf = df_mtf['c'].astype(float).tolist()
                mtf_signal = build_mtf_signals(closes_mtf)[-1] if len(closes_mtf) >= 100 else 0
                with state_lock:
                    shared_state["filtros"]["MTF"] = f"{mtf_signal}/3"
            except Exception as e:
                logging.warning(f"Erro MTF: {e}")
            time.sleep(30)
        except Exception as e:
            logging.error(f"Erro no scanner: {e}")
            time.sleep(10)

def thread_motor():
    global dca_engine
    with engine_lock:
        if dca_engine and dca_engine.cash == CONFIG["CAPITAL_TOTAL"] and not dca_engine.position:
            inicializar_vault()
    with config_lock:
        timeframe = CONFIG.get("TIMEFRAME", "5m")
        symbol = CONFIG["SYMBOL"]
    with engine_lock:
        last_processed = dca_engine.last_candle_time if dca_engine else 0

    while True:
        with state_lock:
            if not shared_state["conn_ok"]:
                time.sleep(5)
                continue
        try:
            if last_processed == 0:
                with exchange_lock:
                    ohlcv = exchange.fetch_ohlcv(symbol, timeframe=timeframe, limit=1)
                if not ohlcv:
                    time.sleep(5)
                    continue
                last_processed = ohlcv[0][0]
                with engine_lock:
                    if dca_engine:
                        dca_engine.last_candle_time = last_processed
                logging.info(f"Motor sincronizado. Último candle em {datetime.fromtimestamp(last_processed/1000)}")
                with state_lock:
                    shared_state["marcha"] = "AGUARDANDO ENTRADA"
                time.sleep(5)
                continue

            with exchange_lock:
                ohlcv = exchange.fetch_ohlcv(symbol, timeframe=timeframe, since=last_processed + 1, limit=1000)
            if len(ohlcv) == 0:
                if timeframe.endswith('m'):
                    candle_duration = int(timeframe[:-1]) * 60
                elif timeframe.endswith('h'):
                    candle_duration = int(timeframe[:-1]) * 3600
                else:
                    candle_duration = 3600
                now = time.time()
                next_candle_time = (last_processed / 1000) + candle_duration
                if now > next_candle_time + 10:
                    logging.warning("Atraso detectado: forçando sincronização.")
                    with exchange_lock:
                        ultimo_candle = exchange.fetch_ohlcv(symbol, timeframe=timeframe, limit=1)
                    if ultimo_candle:
                        last_processed = ultimo_candle[0][0]
                        with engine_lock:
                            if dca_engine:
                                dca_engine.last_candle_time = last_processed
                        continue
                else:
                    sleep_time = max(0, next_candle_time - now)
                    if sleep_time > 0:
                        time.sleep(sleep_time)
                    else:
                        time.sleep(5)
                continue

            for k in ohlcv:
                candle_time = k[0]
                if candle_time <= last_processed:
                    continue
                candle = {
                    't': candle_time,
                    'o': k[1],
                    'h': k[2],
                    'l': k[3],
                    'c': k[4],
                    'v': k[5]
                }
                with engine_lock:
                    if dca_engine:
                        dca_engine.on_candle(candle)
                last_processed = candle_time
                with engine_lock:
                    if dca_engine:
                        dca_engine.last_candle_time = last_processed

                if timeframe.endswith('m'):
                    candle_duration = int(timeframe[:-1]) * 60
                elif timeframe.endswith('h'):
                    candle_duration = int(timeframe[:-1]) * 3600
                else:
                    candle_duration = 3600
                now = time.time()
                next_candle_time = (candle_time / 1000) + candle_duration
                sleep_time = max(0, next_candle_time - now)
                if sleep_time > 0:
                    time.sleep(sleep_time)

            with state_lock:
                shared_state.update(dca_engine.get_state())
                shared_state["cash"] = dca_engine.cash
                if dca_engine.position:
                    shared_state["marcha"] = "DCA ATIVO"
                elif shared_state["marcha"] in ("INICIALIZANDO...", "RECUPERANDO..."):
                    shared_state["marcha"] = "AGUARDANDO ENTRADA"
            time.sleep(1)
        except ccxt.NetworkError as e:
            logging.error(f"Erro de rede no motor: {e}")
            verificar_conexao()
            time.sleep(5)
        except Exception as e:
            with state_lock:
                shared_state["erros_consecutivos"] += 1
                cnt = shared_state["erros_consecutivos"]
            logging.error(f"Erro no motor ({cnt}/5): {e}")
            if cnt >= 5:
                panico_sistema("5 erros consecutivos no Motor.")
            time.sleep(5)

def thread_visual():
    while True:
        if not menu_ativo:
            os.system('cls' if os.name == 'nt' else 'clear')
            uptime = str(datetime.now() - inicio_bot).split('.')[0]
            with state_lock:
                s = dict(shared_state)
            with config_lock:
                cfg_symbol = CONFIG['SYMBOL']
                cfg_max_so = CONFIG['MAX_SAFETY_ORDERS']
                cfg_sl_usd = CONFIG['STOP_LOSS'] * CONFIG['CAPITAL_TOTAL']
                cfg_rsi_max = CONFIG['RSI_MAX_ENTRADA']
                cfg_vol_on = CONFIG.get('FILTRO_VOLUME_ATIVO', True)
                cfg_cb_on = CONFIG.get('CIRCUIT_BREAKER_ATIVO', True)
                cfg_stag_on = CONFIG['STAGNATION_EXIT']
                cfg_range_mode = CONFIG.get('RANGE_MODE_ENABLED', False)
            rsi_tag = f"{Fore.GREEN}ON (limite {cfg_rsi_max:.0f})"
            vol_tag = f"{Fore.GREEN}ON" if cfg_vol_on else f"{Fore.RED}OFF"
            cb_tag  = f"{Fore.GREEN}ON" if cfg_cb_on else f"{Fore.RED}OFF"
            print(f"{Fore.CYAN}🐦‍🔥 PHOENIX REAL v5.8.3 (RANGE MODE) {Fore.WHITE}| UPTIME: {uptime}")
            print(f"{Fore.YELLOW}{'='*80}")
            if s["circuit_breaker"]:
                print(f"{Fore.RED}  ⚡ CIRCUIT BREAKER ATIVO — Entradas pausadas")
            mtf_display = s.get("filtros", {}).get("MTF", "?")
            rsi_cor = Fore.RED if s["rsi_atual"] >= cfg_rsi_max else Fore.GREEN
            print(f"  MERCADO: {Fore.GREEN}{cfg_symbol} {Fore.YELLOW}${s['preco']:.8f} "
                  f"{Fore.WHITE}| MTF {mtf_display} | RSI {rsi_cor}{s['rsi_atual']:.1f}")
            print(f"   STATUS: {Fore.CYAN}{s['marcha']}")
            print(f"  FILTROS: RSI[{rsi_tag}{Fore.WHITE}] VOL[{vol_tag}{Fore.WHITE}] CB[{cb_tag}{Fore.WHITE}]")
            if cfg_range_mode:
                ranging_status = f"{Fore.MAGENTA}RANGE" if dca_engine and dca_engine.is_ranging else f"{Fore.GREEN}TENDÊNCIA"
                print(f"     MODO: {ranging_status}{Fore.WHITE}")
            exit_tags = []
            if cfg_stag_on: exit_tags.append(f"{Fore.YELLOW}Estagnação")
            if exit_tags:
                print(f"   SAÍDAS: {', '.join(exit_tags)}")
            print(f"   REGIME: {Fore.MAGENTA}{s['current_regime']}{Fore.WHITE}")
            conn_status = f"{Fore.GREEN}ONLINE" if s["conn_ok"] else f"{Fore.RED}OFFLINE"
            print(f"  CONEXÃO: {conn_status}{Fore.WHITE}")
            if s["em_operacao"]:
                print(f"{Fore.YELLOW}{'-'*80}")
                pnl     = s['lucro_perc_atual']
                perda   = s['perda_usd_atual']
                cor_pnl = Fore.GREEN if pnl > 0 else Fore.RED
                print(f" P. MÉDIO: {Fore.WHITE}${s['preco_medio']:.8f} "
                      f"{cor_pnl}{pnl:+.2f}%  (${perda:.2f} USD / limite ${cfg_sl_usd:.2f})")
                if cfg_sl_usd > 0:
                    progresso_sl  = min(perda / cfg_sl_usd, 1.0)
                    blocos = int(progresso_sl * 20)
                    barra_sl = "█" * blocos + "░" * (20 - blocos)
                    cor_sl = Fore.GREEN if progresso_sl < 0.5 else Fore.YELLOW if progresso_sl < 0.8 else Fore.RED
                    print(f"   SL USD: {cor_sl}[{barra_sl}] {progresso_sl*100:.0f}%")
                usadas = s['num_safety_orders']
                barra  = "▰" * usadas + "▱" * (cfg_max_so - usadas)
                print(f"   SAFETY: {Fore.YELLOW}{barra} ({usadas}/{cfg_max_so})")
                if s['proxima_compra_p'] > 0:
                    dist = ((s['proxima_compra_p'] / s['preco']) - 1) * 100 if s['preco'] > 0 else 0
                    print(f" DCA PROX: {Fore.RED}${s['proxima_compra_p']:.8f} ({dist:.2f}%)")
                if s['trailing_ativo']:
                    dist_venda = ((s['preco'] / s['stop_atual_trailing']) - 1) * 100 if s['stop_atual_trailing'] > 0 else 0
                    print(f" TRAILING: {Fore.MAGENTA}ATIVO (Stop: ${s['stop_atual_trailing']:.8f} | Recuo: {dist_venda:.2f}%)")
                elif s['alvo_trailing_ativacao'] > 0:
                    dist_alvo = ((s['alvo_trailing_ativacao'] / s['preco']) - 1) * 100 if s['preco'] > 0 else 0
                    print(f"  ALVO TS: {Fore.CYAN}${s['alvo_trailing_ativacao']:.8f} (+{dist_alvo:.2f}%)")
                if s["operating_paused"]:
                    pause_status = f"{Fore.RED}PAUSA ATIVA (sem novas entradas)"
                else:
                    pause_status = f"{Fore.GREEN}HORÁRIO LIVRE"
                print(f"  HORÁRIO: {pause_status}{Fore.WHITE}")
                if "entry_score" in s:
                    entry_score_color = Fore.GREEN if s["entry_score"] >= s.get("entry_score_threshold", 0.75) else Fore.YELLOW
                    print(f" SCORE IN: {entry_score_color}{s['entry_score']:.2f}{Fore.WHITE} / {s.get('entry_score_threshold', 0.75):.2f}")
                if "exit_score" in s:
                    exit_score_color = Fore.RED if s["exit_score"] >= s.get("exit_score_threshold", 8.5) else Fore.GREEN
                    print(f"SCORE OUT: {exit_score_color}{s['exit_score']:.1f}{Fore.WHITE} / {s.get('exit_score_threshold', 8.5):.1f}")
            print(f"{Fore.YELLOW}{'='*80}")
            print(f" LOG: {s['msg_log']}")
            print(f"{Fore.YELLOW}{'='*80}")
            print(f" {Fore.WHITE}[Ctrl+C] MENU | LOGS: {ARQUIVO_LOG_SISTEMA} | TRADES: {ARQUIVO_LOG_TRADES}")
        time.sleep(1)

def thread_ticker_ws():
    async def ws_loop():
        with config_lock:
            ultimo_symbol = CONFIG['SYMBOL']
        uri = f"wss://stream.binance.com:9443/ws/{ultimo_symbol.replace('/', '').lower()}@ticker"
        while True:
            with state_lock:
                if not shared_state["conn_ok"]:
                    await asyncio.sleep(5)
                    continue
            try:
                with config_lock:
                    cur = CONFIG['SYMBOL']
                if ultimo_symbol != cur:
                    ultimo_symbol = cur
                    uri = f"wss://stream.binance.com:9443/ws/{ultimo_symbol.replace('/', '').lower()}@ticker"
                async with websockets.connect(uri) as ws:
                    while True:
                        with config_lock:
                            cur = CONFIG['SYMBOL']
                        if ultimo_symbol != cur:
                            break
                        try:
                            msg = await asyncio.wait_for(ws.recv(), timeout=2.0)
                            dados = json.loads(msg)
                            current_price = float(dados['c'])
                            with state_lock:
                                shared_state["preco"] = current_price
                                if shared_state.get("em_operacao", False):
                                    if current_price > shared_state["high_intrabar"]:
                                        shared_state["high_intrabar"] = current_price
                                        shared_state["high_intrabar_timestamp"] = int(time.time() * 1000)
                        except asyncio.TimeoutError:
                            continue
            except Exception as e:
                logging.warning(f"WebSocket error: {e}")
                await asyncio.sleep(2)
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    loop.run_until_complete(ws_loop())

def thread_spike_detector():
    global spike_detector
    while True:
        with state_lock:
            if not shared_state["conn_ok"]:
                time.sleep(5)
                continue
        if spike_detector and spike_detector.enabled:
            spike_detector.update_indicators()
        time.sleep(5)

def thread_conection_monitor():
    while True:
        verificar_conexao()
        time.sleep(10)

def thread_operating_hours():
    while True:
        with state_lock:
            shared_state["operating_paused"] = is_paused_time()
        time.sleep(60)

# =============================================================================
# MENU INTERATIVO
# =============================================================================

def acionar_menu(signum, frame):
    global menu_ativo
    menu_ativo = True
    os.system('cls' if os.name == 'nt' else 'clear')
    print(f"{Fore.MAGENTA}╔══════════════════════════════════════╗")
    print(f"{Fore.MAGENTA}║    MENU DE CONTROLE PHOENIX v5.8.3   ║")
    print(f"{Fore.MAGENTA}╠══════════════════════════════════════╣")
    print(f"{Fore.WHITE}║ 1. VOLTAR AO MONITORAMENTO           ║")
    print(f"{Fore.RED}║ 2. ENCERRAR (DESLIGAR BOT)           ║")
    print(f"{Fore.MAGENTA}╚══════════════════════════════════════╝")
    try:
        opt = input(f"\n{Fore.CYAN}➤ Escolha uma opção [1-2]: {Fore.WHITE}")
        if opt == '1':
            print(f"{Fore.GREEN}Retornando...")
            time.sleep(0.5)
        elif opt == '2':
            print(f"{Fore.RED}Salvando dados e encerrando...")
            salvar_estado_disco()
            sys.exit(0)
        else:
            print(f"{Fore.RED}Opção inválida.")
            time.sleep(1)
    except KeyboardInterrupt:
        print(f"\n{Fore.RED}Forçando saída...")
        salvar_estado_disco()
        sys.exit(0)
    except Exception as e:
        print(f"Erro no menu: {e}")
        time.sleep(1)
    menu_ativo = False

# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    signal.signal(signal.SIGINT, acionar_menu)
    carregar_configuracoes()
    if exchange is None:
        print("Falha na inicialização da exchange. Encerrando.")
        sys.exit(1)
    threading.Thread(target=thread_conection_monitor, daemon=True, name="ConnMonitor").start()
    threading.Thread(target=thread_motor,     daemon=True, name="Motor").start()
    if CONFIG.get("SPIKE_ENABLED", False):
        threading.Thread(target=thread_spike_detector, daemon=True, name="SpikeDetector").start()
    threading.Thread(target=thread_visual,    daemon=True, name="Visual").start()
    threading.Thread(target=thread_ticker_ws, daemon=True, name="TickerWS").start()
    threading.Thread(target=thread_scanner,   daemon=True, name="Scanner").start()
    threading.Thread(target=thread_operating_hours, daemon=True, name="OperatingHours").start()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        salvar_estado_disco()
        sys.exit(0)
