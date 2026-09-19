# Diagonal restriction Pi = P: phi(a,b) = R0(a,b)(a^b) in Alt_n; class modulo <a,b,ab> (n odd so that n-3 is even).
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
def matchings(idx):
    if not idx: yield []; return
    a=idx[0]
    for t in range(1,len(idx)):
        b=idx[t]; rest=idx[1:t]+idx[t+1:]
        for mm in matchings(rest): yield [(a,b)]+mm
SUB=subspaces(n); PLV=[pl(a,b) for (a,b) in SUB]
EV=[]
for (a,b) in SUB:
    gens=[a,b,a&b]
    sp=[u for u in range(1,1<<n) if not (PAR[u&a]|PAR[u&b]|PAR[u&(a&b)])]
    basis=[]; S={0}
    for u in sp:
        if u not in S: basis.append(u); S|={s^u for s in S}
    if len(basis)==n-3:
        EV.append([[pl(basis[i],basis[j]) for (i,j) in mt] for mt in matchings(list(range(n-3)))])
    else: EV.append(None)
print("n",n,"planes",len(SUB),"generic:",sum(1 for e in EV if e),flush=True)
par=lambda x: bin(x).count('1')&1
rnd=random.Random(seed)
for t in range(trials):
    D=[[ (0 if t==0 else rnd.getrandbits(N)) for _ in range(N)] for _ in range(N)]
    cnt=0
    for idx,(a,b) in enumerate(SUB):
        if EV[idx] is None: continue
        q=PLV[idx]; r=0
        for j,(c,d) in enumerate(pairs):
            if q>>j&1:
                if (a>>c&1)&(b>>d&1): r^=1<<j
                for i in range(N):
                    if q>>i&1: r^=D[i][j]
        pf=0
        for mt in EV[idx]:
            ok=1
            for msk in mt:
                if not par(r&msk): ok=0;break
            pf^=ok
        cnt+=pf
    print("sorted" if t==0 else "random","count",cnt,"parity",cnt&1,flush=True)
