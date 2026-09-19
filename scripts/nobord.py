# Simplified invariant (no border, n even): coefficient of nu = prod_i a_i b_i in Pf(G), G_e = sorted + random Psi + random lower-degree contamination.
import random, sys, itertools
n=int(sys.argv[1]); trials=int(sys.argv[2]); dens=float(sys.argv[3])
Z=tuple([0]*n)
def ok(mon): return all(x<=1 for x in mon[0]) and all(x<=1 for x in mon[1])
def padd(p,q): r=set(p); r^=set(q); return r
def pmul(p,q):
    r=set()
    for (a1,b1) in p:
        for (a2,b2) in q:
            mon=(tuple(x+y for x,y in zip(a1,a2)),tuple(x+y for x,y in zip(b1,b2)))
            if ok(mon): r^={mon}
    return r
def va(i): e=[0]*n; e[i]=1; return {(tuple(e),Z)}
def vb(i): e=[0]*n; e[i]=1; return {(Z,tuple(e))}
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]
P={(c,d): padd(pmul(va(c),vb(d)),pmul(va(d),vb(c))) for (c,d) in pairs}
def matchings(idx):
    if not idx: yield []; return
    a=idx[0]
    for t in range(1,len(idx)):
        b=idx[t]; rest=idx[1:t]+idx[t+1:]
        for mm in matchings(rest): yield [(a,b)]+mm
nu=(tuple([1]*n),tuple([1]*n))
rnd=random.Random(5)
def rand_low():
    r=set()
    for _ in range(8):
        da=rnd.randrange(3); db=rnd.randrange(3)
        if (da,db)==(2,2): continue
        ea=[0]*n; eb=[0]*n
        for _ in range(da): ea[rnd.randrange(n)]+=1
        for _ in range(db): eb[rnd.randrange(n)]+=1
        mon=(tuple(ea),tuple(eb))
        if ok(mon): r^={mon}
    return r
for t in range(trials):
    G={}
    for e in pairs:
        k,l=e
        # full sorted term a_k b_l p_kl, but squares pruned by ok()
        g=pmul(pmul(va(k),vb(l)),P[e])
        if t>0:
            for ij in pairs:
                for cd in pairs:
                    if rnd.random()<dens: g=padd(g,pmul(P[ij],P[cd]))
            g=padd(g,rand_low())
        G[e]=g
    tot=set()
    for M in matchings(list(range(n))):
        term={(Z,Z)}
        for e in M: term=pmul(term,G[e])
        tot=padd(tot,term)
    print("n",n,"trial",t,"coeff of nu in Pf(G):",1 if nu in tot else 0)
