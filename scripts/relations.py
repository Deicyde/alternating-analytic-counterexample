# For random half-selectors h over F_2 (h(e_i^e_j)=E_ij+S_ij, S_ij symmetric), compute for each 2-dim subspace <x,y>
# delta(w)=1 iff the bilinear form h(w) restricted to {x,y}^perp (dim n-2) is nondegenerate. Then find universal affine relations.
import random, sys
from halfsel import subspaces, plucker, rank_rows
def perp_basis(n,x,y):
    # basis of {z : z.x = z.y = 0} over F2
    vecs=[z for z in range(1,1<<n) if bin(z&x).count('1')%2==0 and bin(z&y).count('1')%2==0]
    basis=[]; span={0}
    for z in vecs:
        if z not in span:
            basis.append(z); span|={s^z for s in span}
    return basis
def form_on(n,rows,basis):
    m=len(basis); out=[]
    for a in basis:
        r=0
        # a^T G
        vec=0
        for k in range(n):
            if a>>k&1: vec^=rows[k]
        for bi,b in enumerate(basis):
            if bin(vec&b).count('1')%2: r|=1<<bi
        out.append(r)
    return out
def rand_G(n,rnd,schur=False):
    G={}
    for i in range(n):
        for j in range(i+1,n):
            rows=[0]*n; rows[i]|=1<<j
            if schur:
                if rnd.random()<0.5:
                    rows[i]^=1<<j; rows[j]^=1<<i
            else:
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
        f=form_on(n,rows,PERP[idx])
        if rank_rows(f)==n-2: v|=1<<idx
    return v
n=int(sys.argv[1]); trials=int(sys.argv[2]); schur=len(sys.argv)>3
rnd=random.Random(1)
SUB=subspaces(n); PERP=[perp_basis(n,x,y) for (x,y) in SUB]
m=len(SUB)
vecs=[]; zero_count=0; minw=10**9
for t in range(trials):
    v=delta_vec(n,rand_G(n,rnd,schur),SUB,PERP)
    w=bin(v).count('1'); minw=min(minw,w)
    if v==0: zero_count+=1
    vecs.append(v|(1<<m))   # append constant 1
print("n",n,"subspaces",m,"trials",trials,"delta==0 cases:",zero_count,"min #nonzero:",minw)
# nullspace of functionals: find all c in F2^{m+1} with <c,v>=0 for all v  (c_m=1 means sum_{T} delta = 1)
# Gaussian elimination on the span of vecs; annihilator dimension = m+1-rank
basis=[]
for v in vecs:
    for b in basis: v=min(v,v^b)
    if v: basis.append(v)
print("rank of span:",len(basis),"of",m+1,"=> universal affine relations:",m+1-len(basis))
