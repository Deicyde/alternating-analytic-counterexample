# Affine-linear system over F_2: R0(z,z')(v^w) in (PiP)^V  for GENERIC pairs only (dim PiP = 4).
import sys, random
from halfsel import subspaces
n=int(sys.argv[1]); maxeq=int(sys.argv[2]); seed=int(sys.argv[3]) if len(sys.argv)>3 else 0
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]; N=len(pairs)
def pl(x,y):
    m=0
    for i,(c,d) in enumerate(pairs):
        if ((x>>c&1)&(y>>d&1))^((x>>d&1)&(y>>c&1)): m|=1<<i
    return m
PAR=[bin(u).count('1')&1 for u in range(1<<n)]
SUB=subspaces(n); PLV=[pl(v,w) for (v,w) in SUB]; m=len(SUB)
nun=N*N*N; CONST=1<<nun
rnd=random.Random(seed)
piv={}
def add(row):
    while row:
        if row==CONST: return False
        p=(row&(CONST-1)).bit_length()-1
        if p in piv: row^=piv[p]
        else: piv[p]=row; return True
    return True
cnt=0; tried=0; incons=False
while cnt<maxeq and tried<50*maxeq:
    tried+=1
    ia=rnd.randrange(m); ib=rnd.randrange(m)
    z,zp=SUB[ia]; v,w=SUB[ib]
    vs=[z&v,z&w,zp&v,zp&w]
    sp=[u for u in range(1,1<<n) if not (PAR[u&vs[0]]|PAR[u&vs[1]]|PAR[u&vs[2]]|PAR[u&vs[3]])]
    if len(sp)!=(1<<(n-4))-1: continue
    basis=[]; S={0}
    for u in sp:
        if u not in S: basis.append(u); S|={s^u for s in S}
    q=PLV[ia]; p=PLV[ib]
    for i1 in range(len(basis)):
        for i2 in range(i1+1,len(basis)):
            mask=pl(basis[i1],basis[i2]); row=0; c0=0
            for j,(c,d) in enumerate(pairs):
                if (p>>j&1) and (mask>>j&1) and (z>>c&1)&(zp>>d&1): c0^=1
            if c0: row^=CONST
            for ab in range(N):
                if q>>ab&1:
                    for cd in range(N):
                        if p>>cd&1: row^=mask<<((ab*N+cd)*N)
            if not add(row): incons=True; break
            cnt+=1
        if incons: break
    if incons: break
print("n",n,"INCONSISTENT" if incons else "consistent","after",cnt,"equations; rank",len(piv),"of",nun)
