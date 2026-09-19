# n=6 (or any even n): diagonal-operator lift model over F_2; delta(Pi,P)=bordered Pfaffian:
#   = class of R(z,z')(v^w) in Lambda^2(V/PiP) when dim PiP = 4 and n-4 = 2, else 0.
import random, sys
from halfsel import subspaces
n=int(sys.argv[1]); trials=int(sys.argv[2]); seed=int(sys.argv[3]) if len(sys.argv)>3 else 0
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]; N=len(pairs)
def pl(x,y):
    m=0
    for i,(c,d) in enumerate(pairs):
        if ((x>>c&1)&(y>>d&1))^((x>>d&1)&(y>>c&1)): m|=1<<i
    return m
PAR=[bin(u).count('1')&1 for u in range(1<<n)]
def perp(vs):
    sp=[u for u in range(1,1<<n) if not (PAR[u&vs[0]]|PAR[u&vs[1]]|PAR[u&vs[2]]|PAR[u&vs[3]])]
    return sp
SUB=subspaces(n); PLV=[pl(v,w) for (v,w) in SUB]
print("n",n,"planes",len(SUB),flush=True)
EV=[]   # per Pi: list of (ib, mask)
tot=0
for ia,(z,zp) in enumerate(SUB):
    row=[]
    for ib,(v,w) in enumerate(SUB):
        sp=perp([z&v,z&w,zp&v,zp&w])
        if len(sp)==3:     # 2-dim perp: nonzero vectors u1,u2,u1+u2
            row.append((ib,pl(sp[0],sp[1])))
    EV.append(row); tot+=len(row)
print("generic pairs (dim PiP = 4):",tot,flush=True)
par=lambda m: bin(m).count('1')&1
rnd=random.Random(seed)
for t in range(trials):
    mode='sorted' if t==0 else 'random'
    D=[[ (rnd.getrandbits(N) if mode=='random' else 0) for _ in range(N)] for _ in range(N)]
    cnt=0
    for ia,(z,zp) in enumerate(SUB):
        q=PLV[ia]; M=[0]*N
        for i in range(N):
            if q>>i&1:
                Di=D[i]
                for j in range(N): M[j]^=Di[j]
        for j,(c,d) in enumerate(pairs):
            if (z>>c&1)&(zp>>d&1): M[j]^=1<<j
        for ib,mask in EV[ia]:
            p=PLV[ib]; r=0; j=0
            while p:
                if p&1: r^=M[j]
                p>>=1; j+=1
            cnt+=par(r&mask)
    print(mode,"count:",cnt,"parity",cnt&1,flush=True)
