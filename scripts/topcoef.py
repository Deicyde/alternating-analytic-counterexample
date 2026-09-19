# Formal check over F_2[a_3..a_n,b_3..b_n] (n=5): coefficient of a3a4a5 b3b4b5 in
#   PP = phi ^ a^2 ^ ab ^ b^2,  phi_kl = a_k b_l p_kl + sum Psi[ij][cd][kl] p_ij p_cd,  a=(1,0,a3,a4,a5), b=(0,1,b3,b4,b5).
import random, itertools, sys
n=5; nv=2*(n-2)
def mono(idx): 
    e=[0]*nv; e[idx]=1; return {tuple(e):1}
def padd(p,q):
    r=dict(p)
    for k in q:
        if k in r: del r[k]
        else: r[k]=1
    return r
def pmul(p,q):
    r={}
    for k1 in p:
        for k2 in q:
            k=tuple(x+y for x,y in zip(k1,k2))
            if k in r: del r[k]
            else: r[k]=1
    return r
ONE={tuple([0]*nv):1}; ZERO={}
A=[ONE,ZERO]+[mono(i) for i in range(n-2)]
B=[ZERO,ONE]+[mono(n-2+i) for i in range(n-2)]
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]; N=len(pairs)
P={ (c,d): padd(pmul(A[c],B[d]),pmul(A[d],B[c])) for (c,d) in pairs}
A2=[pmul(x,x) for x in A]; AB=[pmul(x,y) for x,y in zip(A,B)]; B2=[pmul(y,y) for y in B]
def det3(rows):
    cols=[A2,AB,B2]; r={}
    for perm in itertools.permutations(range(3)):
        t=ONE
        for i,row in enumerate(rows): t=pmul(t,cols[perm[i]][row])
        r=padd(r,t)
    return r
MIN={}
for (k,l) in pairs:
    rows=[i for i in range(n) if i not in (k,l)]; MIN[(k,l)]=det3(rows)
PP2={ (ij,cd): pmul(P[ij],P[cd]) for ij in pairs for cd in pairs}
top=tuple([1]*nv)
rnd=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 0)
# contribution of sorted part
S={}
for (k,l) in pairs:
    S=padd(S,pmul(pmul(pmul(A[k],B[l]),P[(k,l)]),MIN[(k,l)]))
print("sorted part: top coefficient =",1 if top in S else 0)
# contribution of each Psi parameter to the top coefficient
bad=[]
for ij in pairs:
    for cd in pairs:
        for kl in pairs:
            t=pmul(PP2[(ij,cd)],MIN[kl])
            if top in t: bad.append((ij,cd,kl))
print("number of Psi parameters (ij,cd,kl) whose term contributes to the top coefficient:",len(bad),"of",N**3)
print(bad[:12])
