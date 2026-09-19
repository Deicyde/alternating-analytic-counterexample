# Bracket problem (projection L of M_n onto Alt_n, L|Alt = id): L(a (x) b) = [a|b] + sum_{i<j} p_ij(a,b) lam_ij + sum_i a_i b_i kap_i
# Ask: can Pf(L(a(x)b)) = 0 for all a,b in F_2^n (n even)?   (n=4: rank<=2 ; n=6: rank<=4)
import sys, itertools
n=int(sys.argv[1])
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]; N=len(pairs); PI={p:i for i,p in enumerate(pairs)}
out=["(set-logic QF_UF)"]
for i in range(N):
    for kl in range(N): out.append(f"(declare-const l_{i}_{kl} Bool)")
for i in range(n):
    for kl in range(N): out.append(f"(declare-const k_{i}_{kl} Bool)")
def matchings(idx):
    if not idx: yield []; return
    a=idx[0]
    for t in range(1,len(idx)):
        b=idx[t]; rest=idx[1:t]+idx[t+1:]
        for m in matchings(rest): yield [(a,b)]+m
MATCH=list(matchings(list(range(n))))
cnt=0
for a in range(1<<n):
    for b in range(1<<n):
        ent=[]
        for kl,(k,l) in enumerate(pairs):
            const=(a>>k&1)&(b>>l&1)
            terms=[]
            for i,(c,d) in enumerate(pairs):
                if ((a>>c&1)&(b>>d&1))^((a>>d&1)&(b>>c&1)): terms.append(f"l_{i}_{kl}")
            for i in range(n):
                if (a>>i&1)&(b>>i&1): terms.append(f"k_{i}_{kl}")
            if not terms: e="true" if const else "false"
            else:
                e=terms[0] if len(terms)==1 else "(xor "+" ".join(terms)+")"
                if const: e=f"(not {e})"
            ent.append(e)
        prods=[]
        for m in MATCH:
            fs=[ent[PI[p]] for p in m]
            if any(f=="false" for f in fs): continue
            fs=[f for f in fs if f!="true"]
            prods.append("true" if not fs else (fs[0] if len(fs)==1 else "(and "+" ".join(fs)+")"))
        if not prods: continue
        pf=prods[0] if len(prods)==1 else "(xor "+" ".join(prods)+")"
        out.append(f"(assert (not {pf}))"); cnt+=1
out.append("(check-sat)")
open(f"br_{n}.smt2","w").write("\n".join(out)+"\n"); print("n",n,"constraints",cnt)
