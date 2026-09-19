import random, sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
from halfsel import subspaces, plucker, rank_rows
import importlib
def perp_basis(n,x,y):
    vecs=[z for z in range(1,1<<n) if bin(z&x).count('1')%2==0 and bin(z&y).count('1')%2==0]
    basis=[]; span={0}
    for z in vecs:
        if z not in span:
            basis.append(z); span|={s^z for s in span}
    return basis
def form_on(n,rows,basis):
    out=[]
    for a in basis:
        vec=0
        for k in range(n):
            if a>>k&1: vec^=rows[k]
        r=0
        for bi,b in enumerate(basis):
            if bin(vec&b).count('1')%2: r|=1<<bi
        out.append(r)
    return out
def rand_G(n,rnd):
    G={}
    for i in range(n):
        for j in range(i+1,n):
            rows=[0]*n; rows[i]|=1<<j
            for k in range(n):
                for l in range(k,n):
                    if rnd.random()<0.5:
                        rows[k]^=1<<l
                        if k!=l: rows[l]^=1<<k
            G[(i,j)]=rows
    return G
def delta_vec(n,G,SUB,PERP):
    v=0
    for idx,(x,y) in enumerate(SUB):
        rows=[0]*n
        for (i,j) in plucker(n,x,y):
            g=G[(i,j)]
            for k in range(n): rows[k]^=g[k]
        if rank_rows(form_on(n,rows,PERP[idx]))==n-2: v|=1<<idx
    return v
n=int(sys.argv[1]); trials=int(sys.argv[2])
rnd=random.Random(7)
SUB=subspaces(n); PERP=[perp_basis(n,x,y) for (x,y) in SUB]; m=len(SUB)
vecs=[delta_vec(n,rand_G(n,rnd),SUB,PERP)|(1<<m) for _ in range(trials)]
# find c with <c,v>=0 for all v: solve linear system by building matrix rows=vecs, nullspace over F2
rows=vecs[:]
piv={}
for v in rows:
    for p,b in piv.items():
        if v>>p&1: v^=b
    if v:
        p=v.bit_length()-1
        for q in list(piv):
            if piv[q]>>p&1: piv[q]^=v
        piv[p]=v
free=[i for i in range(m+1) if i not in piv]
print("free coords:",free)
for f in free:
    c=1<<f
    for p,b in piv.items():
        if b>>f&1: c|=1<<p
    supp=[i for i in range(m) if c>>i&1]
    print("relation: const term",c>>m&1,"support size",len(supp),"of",m)
    ok=all(bin(c&v).count('1')%2==0 for v in vecs)
    print("verified on samples:",ok)
