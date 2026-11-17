#!/usr/bin/env python3
"""Compare criterion (10-1) (tools/hs_oracle.py) with the explicit families of notes/15 on random
three-column positions with omega <= x < omega^4. Run from the repository root."""
import sys, random
sys.path.insert(0,'scripts'); sys.path.insert(0,'tools')
import hs_check2 as C, hs_oracle as H
C.FIN=C.Finite3(300,40); H.P3_finite=C.is_P3_finite

def fam(cols):
    u,v,x=cols
    i=H.deg(x); xi=H.lead(x); c=H.low(x,i)
    U=H.high(u,i+1); V=H.high(v,i+1); ui=H.coef(u,i); vi=H.coef(v,i); a=H.low(u,i); b=H.low(v,i)
    # U, V as ordinals divided by w^(i+1): finite iff only exponent i+1
    Ufin = (not U) or set(U)=={i+1}
    U0 = U.get(i+1,0) if Ufin else None
    if not U and not V and vi==xi and ui==2*xi:
        return ('ii', a==H.G2(b,c))
    if U and U==V and Ufin and U0==xi and ui==vi:
        return ('iii', c==H.G2(H.nat_add(H.O((i,ui)),a), H.nat_add(H.O((i,vi)),b)))
    if not U and not V and vi>xi and ui==vi+xi:
        return ('iv-a', not H.nim(H.nim(a,b),c))
    if U and U==V and Ufin and U0>=1 and ui>vi and xi==U0+ui-vi:
        return ('iv-b', not H.nim(H.nim(a,b),c))
    return (None, False)

rng=random.Random(3)
def ro(d):
    return {e: rng.randint(1,4 if e else 12) for e in range(d,-1,-1) if rng.random()<0.6}
cnt={}; bad=0; n=0
while n<200000:
    d=rng.randint(1,3)
    cols=sorted([ro(d) for _ in range(3)], key=H.key, reverse=True)
    r=rng.random()
    if r<0.5:  # force interesting coefficient relations
        x=cols[2]
        if H.deg(x)<1: continue
        i=H.deg(x); xi=H.lead(x)
        kind=rng.randint(0,3)
        U0=rng.choice([0,xi,1,2,3])
        vi=rng.choice([xi,xi+1,xi+2,rng.randint(0,5)])
        ui=rng.choice([2*xi,vi+xi,vi,vi+rng.randint(0,3)])
        hi={i+1:U0} if U0 else {}
        if rng.random()<0.2: hi={i+2:1}
        lowa={e:cc for e,cc in ro(i-1).items()} if i>=1 else {}
        lowb={e:cc for e,cc in ro(i-1).items()} if i>=1 else {}
        u=H.nat_add(H.nat_add(hi,H.O((i,ui))),lowa); v=H.nat_add(H.nat_add(hi if rng.random()<0.9 else {},H.O((i,vi))),lowb)
        # pick a, b, c making the top condition hold half the time
        cols=sorted([u,v,x],key=H.key,reverse=True)
    cols=[c for c in cols if c]
    if len(cols)<3 or H.deg(cols[2])<1: continue
    n+=1
    p=H.is_P(cols); f,ok=fam(cols)
    if p!=(f is not None and ok):
        bad+=1
        if bad<10: print('MISMATCH',[H.show(c) for c in cols],p,f,ok)
    if p: cnt[f]=cnt.get(f,0)+1
print('positions',n,'P by family',cnt,'mismatches',bad)
