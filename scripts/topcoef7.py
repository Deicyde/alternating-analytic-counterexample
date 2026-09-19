# Formal check of the key coefficient for n = 5, 7 (and 9 with sparse Psi): coefficient of mu = a_1^2 b_2^2 prod_{i>=3} a_i b_i in
#   PP = G^{[m]} ^ a^2 ^ ab ^ b^2,   G_e = sorted + sum Psi[ij][cd][e] p_ij p_cd + (random lower-order contamination),
# over F_2, with pruning of monomials that do not divide mu.
import random, sys, itertools
n=int(sys.argv[1]); trials=int(sys.argv[2]); dens=float(sys.argv[3]) if len(sys.argv)>3 else 0.5
m=(n-3)//2
MUa=[2,0]+[1]*(n-2); MUb=[0,2]+[1]*(n-2)
def ok(mon):
    ea,eb=mon
    return all(x<=y for x,y in zip(ea,MUa)) and all(x<=y for x,y in zip(eb,MUb))
def padd(p,q):
    r=set(p); r^=set(q); return r
def pmul(p,q):
    r=set()
    for (ea1,eb1) in p:
        for (ea2,eb2) in q:
            mon=(tuple(x+y for x,y in zip(ea1,ea2)),tuple(x+y for x,y in zip(eb1,eb2)))
            if ok(mon): r^={mon}
    return r
Z=tuple([0]*n)
def va(i): 
    e=[0]*n; e[i]=1; return {(tuple(e),Z)}
def vb(i):
    e=[0]*n; e[i]=1; return {(Z,tuple(e))}
ONE={(Z,Z)}
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]
P={(c,d): padd(pmul(va(c),vb(d)),pmul(va(d),vb(c))) for (c,d) in pairs}
PPm={}
def pp(ij,cd):
    if (ij,cd) not in PPm: PPm[(ij,cd)]=pmul(P[ij],P[cd])
    return PPm[(ij,cd)]
# all monomials of bidegree <= (2,2) but not (2,2): contamination basis (sample)
def rand_low(rnd):
    r=set()
    for _ in range(6):
        da=rnd.randrange(3); db=rnd.randrange(3)
        if (da,db)==(2,2): continue
        ea=[0]*n; eb=[0]*n
        for _ in range(da): ea[rnd.randrange(n)]+=1
        for _ in range(db): eb[rnd.randrange(n)]+=1
        mon=(tuple(ea),tuple(eb))
        if ok(mon): r^={mon}
    return r
def matchings(idx):
    if not idx: yield []; return
    a=idx[0]
    for t in range(1,len(idx)):
        b=idx[t]; rest=idx[1:t]+idx[t+1:]
        for mm in matchings(rest): yield [(a,b)]+mm
mu=(tuple(MUa),tuple(MUb))
rnd=random.Random(11)
for t in range(trials):
    G={}
    for e in pairs:
        k,l=e
        g=pmul(pmul(va(k),vb(l)),P[e])
        if t>0:
            for ij in pairs:
                for cd in pairs:
                    if rnd.random()<dens: g=padd(g,pp(ij,cd))
            g=padd(g,rand_low(rnd))
        G[e]=g
    total=set()
    for trip in itertools.permutations(range(n),3):
        i,j,r=trip
        border=pmul(pmul(pmul(va(i),va(i)),pmul(va(j),vb(j))),pmul(vb(r),vb(r)))
        if not border: continue
        rest=[x for x in range(n) if x not in trip]
        for M in matchings(rest):
            term=border
            for e in M:
                term=pmul(term,G[e])
                if not term: break
            total=padd(total,term)
    print("trial",t,"(sorted only)" if t==0 else "(random Psi + contamination)","coefficient of mu:",1 if mu in total else 0,flush=True)
