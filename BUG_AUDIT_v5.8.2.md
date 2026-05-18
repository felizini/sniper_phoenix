# Sniper Phoenix v5.8.2 — Varredura de Bugs

## Escopo
- Arquivo analisado: `deepseek_python_v582.py`.
- Tipo de varredura: leitura estática + validação de compilação Python.

## Achados críticos

### 1) Take-profit parcial pode disparar repetidamente no mesmo nível (erro de estratégia/lógica)
**Problema:** os níveis de TP já executados são verificados via `self._partial_sold_levels`, mas o set nunca é atualizado após venda parcial com sucesso. Isso permite repetir vendas para o mesmo nível em candles subsequentes.

**Evidência:**
- Verificação de níveis já vendidos: `if level not in self._partial_sold_levels ...`.
- Após `_partial_close(...)`, não há `self._partial_sold_levels.add(level)` para os níveis executados.

**Risco operacional:** over-selling/fechamento integral precoce não planejado e distorção de performance.

### 2) Estado `spike_active` pode ficar preso em `True` após venda de SPIKE em alguns fluxos (erro de estado)
**Problema:** em `_sell`, quando `self.dca_engine and self.dca_engine.position` e a venda falha (`if not res['ok']`), a função retorna sem resetar `shared_state["spike_active"]`/`position_active`.

**Evidência:**
- Retorno antecipado em falha de venda unificada.
- Reset de `spike_active` ocorre apenas após o bloco principal, não no retorno antecipado.

**Risco operacional:** bloqueio de novos sinais SPIKE e inconsistência de estado no painel.

### 3) Acesso concorrente sem lock em `shared_state` (race conditions)
**Problema:** há escritas em `shared_state` sem `state_lock` dentro do motor DCA (ex.: `entry_score`, `exit_score`), enquanto outras threads também leem/escrevem este dicionário.

**Evidência:**
- `self.shared_state["entry_score"] = ...` e `self.shared_state["entry_score_threshold"] = ...` sem lock.
- `self.shared_state["exit_score"] = ...` e `self.shared_state["exit_score_threshold"] = ...` sem lock.

**Risco operacional:** estado transitório corrompido, UI inconsistente e decisões baseadas em valores parcialmente atualizados.

## Achados médios

### 4) Fechamento total via `_partial_close` não limpa campos de high intrabar (inconsistência de telemetria)
**Problema:** no caminho de fechamento total em `_partial_close`, reseta `em_operacao/trailing_ativo/max_p_trailing`, mas não limpa `high_intrabar` e `high_intrabar_timestamp` (diferente de `_close_position`).

**Risco:** telemetria/painel pode carregar máximas antigas com posição já encerrada.

### 5) Entrada usa `open` da vela no `_check_entry` em vez de `close` (desalinhamento tático)
**Problema:** `on_candle` chama `_check_entry(open_p, ...)` mesmo com sinais calculados no fechamento (`close`, RSI/BB). Isto pode introduzir preço de entrada artificial na simulação/lógica.

**Risco:** viés de execução e diferença entre sinal e preço usado para entrada.

## Check rápido executado
- `python -m py_compile deepseek_python_v582.py` (sem erro de sintaxe).
