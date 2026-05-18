#!/usr/bin/env python3
import csv, math
from statistics import mean, pstdev
from datetime import datetime

CFG = {
"capital_total":20.0,"capital_base":10.0,"fee_pct":0.075/100,"compound":False,
"max_safety_orders":1,"dca_volume_scale":1.0,"dca_step_initial":0.012,"dca_step_scale":1.2,
"trailing_trigger":0.010,"trailing_dist":0.006,"stop_loss":0.025,
"rsi_max_entrada":65.0,"rsi_period":14,"volume_fator_min":1.5,"atr_period":14,
"entry_score_threshold":0.80,"chandelier_enabled":True,"chandelier_factor":3.0,
"exit_score_threshold":8.5,"take_profit_levels":[2.0,3.5],"take_profit_sizes":[0.4,0.6],
"entry_cooldown":2,"range_mode_enabled":True,"range_adx_threshold":25,"range_bb_period":20,
"range_bb_std":2.0,"range_rsi_oversold":35,"range_rsi_overbought":65,
"range_take_profit_pct":0.01,"range_stop_loss_pct":0.005,"range_use_band_exit":True,
"stagnation_exit":True,"max_candles_no_high":45,"min_profit_pct":0.008,
"ema_cross_exit":True,"min_profit_pct_ema":0.008,"volume_dump_exit":True,
"volume_dump_multiplier":3.5,"volume_dump_drop_pct":0.6/100,"volume_dump_confirm_candles":2,
}

def ema(vals, p):
    a=2/(p+1); out=[]
    e=vals[0]
    for v in vals:
        e=a*v+(1-a)*e; out.append(e)
    return out

def rsi(vals, p=14):
    if len(vals)<p+1: return 50.0
    gains=[]; losses=[]
    for i in range(1,len(vals)):
        d=vals[i]-vals[i-1]; gains.append(max(d,0)); losses.append(max(-d,0))
    ag=sum(gains[:p])/p; al=sum(losses[:p])/p
    for i in range(p,len(gains)):
        ag=(ag*(p-1)+gains[i])/p; al=(al*(p-1)+losses[i])/p
    if al==0: return 100.0 if ag>0 else 50.0
    rs=ag/al; return 100-(100/(1+rs))

def adx(high, low, close, p=14):
    if len(close)<p+1:return 0.0
    tr=[]; pdm=[]; mdm=[]
    for i in range(1,len(close)):
        tr.append(max(high[i]-low[i],abs(high[i]-close[i-1]),abs(low[i]-close[i-1])))
        up=high[i]-high[i-1]; down=low[i-1]-low[i]
        pdm.append(up if up>down and up>0 else 0)
        mdm.append(down if down>up and down>0 else 0)
    atr=sum(tr[:p]); psm=sum(pdm[:p]); msm=sum(mdm[:p])
    dx=[]
    for i in range(p,len(tr)):
        atr=atr-(atr/p)+tr[i]; psm=psm-(psm/p)+pdm[i]; msm=msm-(msm/p)+mdm[i]
        pdi=100*psm/atr if atr else 0; mdi=100*msm/atr if atr else 0
        dx.append(100*abs(pdi-mdi)/(pdi+mdi) if (pdi+mdi) else 0)
    if not dx:return 0.0
    return sum(dx[-p:])/min(p,len(dx))

def bb(vals, p=20, std=2.0):
    if len(vals)<p:return (None,None,None)
    s=vals[-p:]; m=mean(s); sd=pstdev(s)
    return (m+std*sd,m-std*sd,m)

rows=[]
with open('SOLUSDT_2026-05-18_2026-05-18_5m.csv') as f:
    for r in csv.DictReader(f):
        rows.append({k:r[k] for k in r})

cash=CFG['capital_total']; pos=None; cooldown=0; trades=[]; atr=0.0; last_close=None
cl=[]; hi=[]; lo=[]; vol=[]
for i,row in enumerate(rows):
    o=float(row['open']); h=float(row['high']); l=float(row['low']); c=float(row['close']); v=float(row['volume'])
    t=row['open_time_brasilia']
    cl.append(c); hi.append(h); lo.append(l); vol.append(v)
    if last_close is not None:
        tr=max(h-l,abs(h-last_close),abs(l-last_close)); a=2/(CFG['atr_period']+1); atr=a*tr+(1-a)*atr
    last_close=c
    if cooldown>0: cooldown-=1
    rv=rsi(cl,CFG['rsi_period'])
    adxv=adx(hi[-30:],lo[-30:],cl[-30:],14) if len(cl)>=30 else 0
    is_ranging=CFG['range_mode_enabled'] and adxv<CFG['range_adx_threshold']

    if pos is None and len(cl)>=100 and cooldown==0:
        ema25,ema50,ema100=ema(cl,25)[-1],ema(cl,50)[-1],ema(cl,100)[-1]
        mtf=sum([c>ema25,c>ema50,c>ema100])
        vol_ma=mean(vol[-20:]) if len(vol)>=20 else 0
        vol_ratio=(v/vol_ma) if vol_ma else 0
        vol_score=min(2.0,max(0.0,(vol_ratio-CFG['volume_fator_min'])*2)) if vol_ratio>=CFG['volume_fator_min'] else 0
        penalty=max(0,(rv-CFG['rsi_max_entrada'])/10)
        nscore=max(0,(mtf+vol_score-penalty))/5
        entered=False
        if is_ranging:
            up,dn,_=bb(cl,CFG['range_bb_period'],CFG['range_bb_std'])
            if dn and c<=dn and rv<=CFG['range_rsi_oversold']: entered=True
        else:
            if nscore>=CFG['entry_score_threshold']: entered=True
        if entered and cash>=CFG['capital_base']:
            fee=CFG['capital_base']*CFG['fee_pct']; qty=(CFG['capital_base']-fee)/c
            cash-=CFG['capital_base']
            pos={"entry":c,"qty":qty,"cost":CFG['capital_base'],"so":0,"next_dca":c*(1-CFG['dca_step_initial']),"trail":False,"trail_stop":0,"max":c,"maxp":0,"cslh":0,"parts":set()}
            trades.append({"entry_time":t,"entry_price":c,"so":0})

    elif pos is not None:
        pos['max']=max(pos['max'],h); pos['cslh']=0 if h>=pos['max'] else pos['cslh']+1
        pnl_pct=(c/pos['entry']-1)
        pos['maxp']=max(pos['maxp'],pnl_pct)
        # partial TP
        for lvl,size in zip(CFG['take_profit_levels'],CFG['take_profit_sizes']):
            if lvl not in pos['parts'] and pnl_pct>=lvl/100:
                sell_qty=pos['qty']*size; gross=sell_qty*c; fee=gross*CFG['fee_pct']; net=gross-fee
                cost=pos['cost']*(sell_qty/pos['qty']); cash+=net; pos['qty']-=sell_qty; pos['cost']-=cost; pos['parts'].add(lvl)
        if pos['qty']<=1e-12:
            trades[-1].update({"exit_time":t,"exit_price":c,"reason":"TP_MULTI"}); pos=None; cooldown=CFG['entry_cooldown']; continue
        # trailing
        trig=pos['entry']*(1+CFG['trailing_trigger'])
        if not pos['trail'] and h>=trig:
            pos['trail']=True; pos['trail_stop']=pos['max']-(CFG['chandelier_factor']*atr if CFG['chandelier_enabled'] else pos['max']*CFG['trailing_dist'])
        elif pos['trail']:
            new=pos['max']-(CFG['chandelier_factor']*atr if CFG['chandelier_enabled'] else pos['max']*CFG['trailing_dist'])
            if new>pos['trail_stop']: pos['trail_stop']=new
        reason=None
        if pos['trail'] and l<=pos['trail_stop']: reason='TRAILING'
        elif l<=pos['entry']*(1-CFG['stop_loss']): reason='STOP_LOSS'
        elif pos['so']<CFG['max_safety_orders'] and l<=pos['next_dca']:
            dca=CFG['capital_base']*(CFG['dca_volume_scale']**pos['so'])
            if cash>=dca:
                fee=dca*CFG['fee_pct']; add_qty=(dca-fee)/pos['next_dca']; cash-=dca
                pos['cost']+=dca; pos['qty']+=add_qty; pos['entry']=pos['cost']/pos['qty']; pos['so']+=1
                pos['next_dca']=pos['entry']*(1-CFG['dca_step_initial']*(CFG['dca_step_scale']**pos['so']))
                trades[-1]['so']=pos['so']
        if reason:
            gross=pos['qty']*c; fee=gross*CFG['fee_pct']; net=gross-fee; cash+=net
            trades[-1].update({"exit_time":t,"exit_price":c,"reason":reason})
            pos=None; cooldown=CFG['entry_cooldown']

# force close end
if pos is not None:
    c=float(rows[-1]['close']); t=rows[-1]['open_time_brasilia']
    gross=pos['qty']*c; fee=gross*CFG['fee_pct']; cash+=gross-fee
    trades[-1].update({"exit_time":t,"exit_price":c,"reason":"FORCED_EOD"})

wins=0; lines=[]
for tr in trades:
    ep=tr['entry_price']; xp=tr.get('exit_price',ep)
    pnl=(xp/ep-1)*100
    if pnl>0:wins+=1
    lines.append((tr['entry_time'],tr.get('exit_time','-'),ep,xp,tr.get('reason','OPEN'),tr['so'],pnl))

print(f"Candles: {len(rows)} | Trades: {len(trades)} | Wins: {wins}")
print(f"Capital inicial: {CFG['capital_total']:.4f} | final: {cash:.4f} | PnL: {cash-CFG['capital_total']:.4f} ({(cash/CFG['capital_total']-1)*100:.2f}%)")
for i,l in enumerate(lines,1):
    print(i,l)

with open('simulation_report.md','w') as f:
    f.write('# Simulação SOL/USDT (5m)\n')
    f.write(f'- Candles analisados: {len(rows)}\n')
    f.write(f'- Trades: {len(trades)} (wins: {wins}, losses: {len(trades)-wins})\n')
    f.write(f'- Capital inicial: {CFG["capital_total"]:.2f} USDT\n')
    f.write(f'- Capital final: {cash:.4f} USDT\n')
    f.write(f'- PnL líquido: {cash-CFG["capital_total"]:.4f} USDT ({(cash/CFG["capital_total"]-1)*100:.2f}%)\n\n')
    f.write('## Operações\n')
    f.write('| # | Entrada | Saída | Preço entrada | Preço saída | Motivo | SO | PnL % |\n')
    f.write('|---|---|---|---:|---:|---|---:|---:|\n')
    for i,(en,ex,ep,xp,m,so,pnl) in enumerate(lines,1):
        f.write(f'| {i} | {en} | {ex} | {ep:.6f} | {xp:.6f} | {m} | {so} | {pnl:.2f}% |\n')
