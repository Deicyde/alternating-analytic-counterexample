# Finite model over F_2: linear half-selector h: Alt_n -> M_n, h(B)+h(B)^T=B.
# h(e_i^e_j) = E_ij + S_ij, S_ij symmetric. Minimise max rank of h(x^y) over all 2-dim subspaces <x,y>.
import random, sys, itertools
def rank_rows(rows):
    rows=list(rows); r=0
    while rows:
        p=rows.pop()
        if p:
            r+=1; lb=p&-p
            rows=[q^p if q&lb else q for q in rows]
    return r
def subspaces(n):
    seen=set(); out=[]
    for x in range(1,1<<n):
        for y in range(x+1,1<<n):
            key=frozenset((x,y,x^y))
            if key in seen: continue
            seen.add(key); out.append((x,y))
    return out
def plucker(n,x,y):
    return [(i,j) for i in range(n) for j in range(i+1,n) if ((x>>i&1)&(y>>j&1))^((x>>j&1)&(y>>i&1))]
def mat_of(n,G,pl):
    rows=[0]*n
    for (i,j) in pl:
        g=G[(i,j)]
        for k in range(n): rows[k]^=g[k]
    return rows
def evaluate(n,G,PL,target):
    worst=0; pen=0
    for pl in PL:
        r=rank_rows(mat_of(n,G,pl))
        if r>worst: worst=r
        if r>target: pen+=(r-target)
    return worst,pen
def sorted_G(n):
    G={}
    for i in range(n):
        for j in range(i+1,n):
            rows=[0]*n; rows[i]|=1<<j; G[(i,j)]=rows
    return G
def search(n,target,iters,seed=0):
    rnd=random.Random(seed)
    PL=[plucker(n,x,y) for (x,y) in subspaces(n)]
    G=sorted_G(n)
    w,p=evaluate(n,G,PL,target)
    best=(w,p)
    pairs=list(G.keys())
    T=1.0
    for it in range(iters):
        ij=rnd.choice(pairs); k=rnd.randrange(n); l=rnd.randrange(n)
        g=G[ij]
        g[k]^=1<<l
        if k!=l: g[l]^=1<<k
        w2,p2=evaluate(n,G,PL,target)
        if p2<=p or rnd.random()<pow(2.718,-(p2-p)/T):
            w,p=w2,p2
            if p==0: return True,G,it
        else:
            g[k]^=1<<l
            if k!=l: g[l]^=1<<k
        T=max(0.05,T*0.9995)
    return False,G,(w,p)
if __name__=="__main__":
    n=int(sys.argv[1]); target=int(sys.argv[2]); iters=int(sys.argv[3])
    PL=[plucker(n,x,y) for (x,y) in subspaces(n)]
    print("n",n,"subspaces",len(PL),"sorted worst",evaluate(n,sorted_G(n),PL,target))
    for seed in range(int(sys.argv[4]) if len(sys.argv)>4 else 3):
        ok,G,info=search(n,target,iters,seed)
        print("seed",seed,"target",target,"found" if ok else "not found",info if not ok else "at iter %s"%info)
        if ok:
            for ij in sorted(G): print(ij,[format(r,'0%db'%n)[::-1] for r in G[ij]])
            break
