# sniper_phoenix
Repositório integrado com o ChatGPT

# 🔥 Sniper Phoenix

**Sniper Phoenix** é uma plataforma de trading quantitativo para criptomoedas desenvolvida em Python.

O projeto foi criado para permitir o desenvolvimento, otimização e execução de estratégias utilizando exatamente o mesmo núcleo de negociação tanto em **backtests** quanto em **operações ao vivo**, reduzindo diferenças entre simulação e produção.

---

## Principais recursos

* Estratégias configuráveis por arquivo
* Sistema de DCA (Dollar Cost Averaging)
* Entradas por confirmação de tendência
* Stops baseados em ATR
* Trailing Stop
* Realização parcial de lucros
* Controle de risco por operação
* Simulação de taxas e slippage da Binance
* Backtesting com dados históricos
* Walk-Forward Analysis
* Simulações de Monte Carlo
* Otimizador automático de parâmetros
* Relatórios em HTML
* Logs detalhados de execução

---

## Indicadores disponíveis

* EMA 20
* EMA 50
* EMA 200
* RSI
* MACD
* ADX
* ATR
* Bollinger Bands
* Keltner Channels
* OBV
* VWAP

---

## Estrutura do projeto

```text
sniper_phoenix/
│
├── config/
├── core/
├── data/
├── strategies/
├── indicators/
├── backtest/
├── optimizer/
├── reports/
├── logs/
├── utils/
├── tests/
│
├── main.py
├── requirements.txt
└── README.md
```

---

## Instalação

Clone o repositório:

```bash
git clone https://github.com/felizini/sniper_phoenix.git
```

Entre na pasta:

```bash
cd sniper_phoenix
```

Crie um ambiente virtual:

### Windows

```bash
python -m venv .venv
.venv\Scripts\activate
```

### Linux

```bash
python3 -m venv .venv
source .venv/bin/activate
```

Instale as dependências:

```bash
pip install -r requirements.txt
```

---

## Configuração

As configurações do robô são definidas através de arquivos localizados na pasta:

```text
config/
```

Exemplo:

```ini
SYMBOL = BTC/USDT
TIMEFRAME = 5m
CAPITAL_TOTAL = 500
RISK_PER_TRADE = 1.0
```

---

## Executando

Modo Trading:

```bash
python main.py
```

Modo Backtest:

```bash
python backtest.py
```

---

## Objetivos do projeto

O Sniper Phoenix busca oferecer:

* Alta confiabilidade
* Código modular
* Estratégias facilmente extensíveis
* Resultados reproduzíveis
* Ambiente único para pesquisa e produção

---

## Roadmap

### Versão 2.0

* [x] Arquitetura unificada
* [ ] Motor de backtest
* [ ] Sistema de estratégias
* [ ] Gestão de risco
* [ ] Otimizador
* [ ] Walk Forward
* [ ] Monte Carlo
* [ ] Dashboard HTML
* [ ] Operação em tempo real
* [ ] Interface Web

---

## Licença

Este projeto é distribuído sob a licença MIT.

---

## Aviso

Este software é destinado para fins educacionais e de pesquisa.

Operações em criptomoedas envolvem riscos significativos. Não existe garantia de lucro e perdas financeiras podem ocorrer.

O usuário é integralmente responsável pelas decisões tomadas durante a utilização deste software.
