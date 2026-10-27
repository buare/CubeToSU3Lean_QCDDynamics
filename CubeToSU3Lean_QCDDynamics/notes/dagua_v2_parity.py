"""RULES_V2 第二版字典 vs 玄空大卦：六爻陽數奇偶（上元/下元）在字典裡是什麼。字典定義抄自 rules_v2_check.py。"""
import itertools
from fractions import Fraction as F
from collections import Counter, defaultdict
HEX = list(itertools.product((0,1), repeat=6))            # (初,二,三,四,五,上)
inner = lambda y: (y[0], y[2], y[4]); outer = lambda y: (y[1], y[3], y[5])
def state(y):                                              # 第二版：c = 色陽數，w2 = 外卦陰陽，w1 = (c+w2) mod 2
    c = sum(inner(y)); w2 = sum(outer(y)) % 2; w1 = (c + w2) % 2
    return c, w1, w2
def particle(c, w1, w2):
    Q = w1 - F(c,3); t3 = F(w1-w2,2); Y = F(w1+w2,2) - F(c,3)
    if w1 != w2:
        nm = {1:"u_L" if w1 else "d_L", 3:"ν_L" if w1 else "e_L"}[c]
    else:
        nm = {(0,0):"ν^c",(2,0):"u^c",(0,1):"e^c",(2,1):"d^c"}[(c,w1)]
    return nm, Q, t3, Y
N = {(0,0,0):1,(0,1,1):2,(1,0,1):3,(1,1,0):4,(0,0,1):6,(0,1,0):7,(1,0,0):8,(1,1,1):9}
rows = []
for y in HEX:
    c,w1,w2 = state(y); nm,Q,t3,Y = particle(c,w1,w2)
    par6 = sum(y) % 2
    up, lo = y[3:], y[:3]; yun = N[tuple(a^b for a,b in zip(up,lo))]
    rows.append(dict(y=y,nm=nm,Q=Q,t3=t3,Y=Y,w1=w1,par6=par6,yun=yun))
# 1. 六爻奇偶 = 弱1
assert all(r["par6"] == r["w1"] for r in rows); print("1. 六爻陽數奇偶 = 弱1 位元：64 卦全部成立")
# 2. 上元(偶) / 下元(奇) 各含哪些粒子
for p,lab in ((0,"上元（陽數偶）"),(1,"下元（陽數奇）")):
    cnt = Counter(r["nm"] for r in rows if r["par6"]==p); qs = sorted({r["Q"] for r in rows if r["par6"]==p})
    print(f"2. {lab}：{dict(cnt)}；電荷 {[str(q) for q in qs]}；電荷和 {sum(r['Q'] for r in rows if r['par6']==p)}")
assert all(r["Q"] <= 0 for r in rows if r["par6"]==0) and all(r["Q"] >= 0 for r in rows if r["par6"]==1)
# 3. 每一卦只屬於 16 個態之一（一種手徵）：16 個態各出現幾次
st16 = Counter((inner(y),)+state(y)[1:] for y in HEX); assert len(st16)==16 and set(st16.values())=={4}
print("3. 64 卦 = 16 個態 × 4 個外卦方向；16 個態全是 SO(10) 同一個手徵（左手場與右手場的共軛）")
# 4. 變一爻：電荷變化與是否跨元
d = defaultdict(Counter)
for r in rows:
    for k in range(6):
        y2 = tuple(1-v if i==k else v for i,v in enumerate(r["y"])); r2 = rows[HEX.index(y2)]
        d[("內卦爻" if k in (0,2,4) else "外卦爻")][str(r2["Q"]-r["Q"])] += 1
for k,v in d.items(): print(f"4. 變一個{k}：電荷變化分佈 {dict(v)}（每次都跨元）")
# 5. 卦運（上下疊）和粒子的關係
tab = defaultdict(Counter)
for r in rows: tab[r["yun"]][r["nm"]] += 1
print("5. 卦運 vs 粒子（每運 8 卦）：")
for yv in (1,6,7,8,2,3,4,9): print(f"   {yv}運：{dict(tab[yv])}")
