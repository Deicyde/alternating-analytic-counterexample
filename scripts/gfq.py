# Test over F_q (q=4 or 8): for random F_q-linear half-selectors h on Alt_n(F_q), count 2-dim subspaces P with h(w_P)|_{P^perp} nondegenerate.
import random, sys, itertools
def make_field(e):
    mod={1:0b11,2:0b111,3:0b1011,4:0b10011}[e]; q=1<<e
    def mul(a,b):
        r=0
        while b:
            if b&1: r^=a
            b>>=1; a<<=1
            if a&q: a^=mod
        return r
    MUL=[[mul(a,b) for b in range(q)] for a in range(q)]
    INV=[0]*q
    for a in range(1,q):
        for b in range(1,q):
            if MUL[a][b]==1: INV[a]=b
    return q,MUL,INV
def rank(M,MUL,INV):
    M=[r[:] for r in M]; rk=0; rows=len(M); cols=len(M[0]) if M else 0
    for c in range(cols):
        p=None
        for r in range(rk,rows):
            if M[r][c]: p=r;break
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        iv=INV[M[rk][c]]
        M[rk]=[MUL[iv][v] for v in M[rk]]
        for r in range(rows):
            if r!=rk and M[r][c]:
                f=M[r][c]; M[r]=[M[r][t]^MUL[f][M[rk][t]] for t in range(cols)]
        rk+=1
    return rk
def nullspace(A,ncols,MUL,INV):
    # basis of {z: A z = 0}
    M=[r[:] for r in A]; piv=[]; rk=0
    for c in range(ncols):
        p=None
        for r in range(rk,len(M)):
            if M[r][c]: p=r;break
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        iv=INV[M[rk][c]]; M[rk]=[MUL[iv][v] for v in M[rk]]
        for r in range(len(M)):
            if r!=rk and M[r][c]:
                f=M[r][c]; M[r]=[M[r][t]^MUL[f][M[rk][t]] for t in range(ncols)]
        piv.append(c); rk+=1
    free=[c for c in range(ncols) if c not in piv]
    basis=[]
    for f in free:
        z=[0]*ncols; z[f]=1
        for i,c in enumerate(piv): z[c]=M[i][f]
        basis.append(z)
    return basis
def main():
    e=int(sys.argv[1]); n=int(sys.argv[2]); trials=int(sys.argv[3])
    q,MUL,INV=make_field(e); rnd=random.Random(5)
    # enumerate 2-dim subspaces via RREF
    subs=[]
    for a in range(n):
        for b in range(a+1,n):
            freex=[i for i in range(a+1,n) if i!=b]; freey=list(range(b+1,n))
            for vx in itertools.product(range(q),repeat=len(freex)):
                for vy in itertools.product(range(q),repeat=len(freey)):
                    x=[0]*n; y=[0]*n; x[a]=1; y[b]=1
                    for i,v in zip(freex,vx): x[i]=v
                    for i,v in zip(freey,vy): y[i]=v
                    subs.append((x,y))
    print("q",q,"n",n,"subspaces",len(subs))
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    perps=[nullspace([x,y],n,MUL,INV) for (x,y) in subs]
    results=[]
    for t in range(trials):
        G={}
        for (i,j) in pairs:
            g=[[0]*n for _ in range(n)]; g[i][j]=1
            for k in range(n):
                for l in range(k,n):
                    v=rnd.randrange(q); g[k][l]^=v
                    if k!=l: g[l][k]^=v
            G[(i,j)]=g
        cnt=0
        for (x,y),R in zip(subs,perps):
            M=[[0]*n for _ in range(n)]
            for (i,j) in pairs:
                p=MUL[x[i]][y[j]]^MUL[x[j]][y[i]]
                if p:
                    g=G[(i,j)]
                    for k in range(n):
                        for l in range(n): M[k][l]^=MUL[p][g[k][l]]
            # form on R: R M R^T
            m=len(R)
            S=[[0]*m for _ in range(m)]
            for u in range(m):
                Mu=[0]*n
                for l in range(n):
                    acc=0
                    for k in range(n): acc^=MUL[R[u][k]][M[k][l]]
                    Mu[l]=acc
                for v in range(m):
                    acc=0
                    for l in range(n): acc^=MUL[Mu[l]][R[v][l]]
                    S[u][v]=acc
            if rank(S,MUL,INV)==m: cnt+=1
        results.append(cnt)
    print("counts of nondegenerate subspaces:",results)
    print("parities:",[c%2 for c in results],"min",min(results))
main()
