import itertools, sys
sys.argv=['x','7','none']
import sym_lemmaA as S
n=S.n; pairs=S.pairs
G = S.build_G("sym")
# add contamination of bidegree (3,1) and (1,3)  (total degree 4, but NOT componentwise <=(2,2))
def addc(e, A, B, name):
    ea=[0]*n; eb=[0]*n
    for i in A: ea[i]+=1
    for i in B: eb[i]+=1
    G[e]=S.padd(G[e], {(tuple(ea),tuple(eb)): S.cvar(name)})
for e in pairs:
    for A in itertools.combinations_with_replacement(range(n),3):
        for B in range(n):
            if S.div_mu(tuple(sum(1 for x in A if x==i) for i in range(n)),
                        tuple(1 if i==B else 0 for i in range(n))):
                addc(e, A, [B], "D%s_%s_%s"%(e,A,B))
    for A in range(n):
        for B in itertools.combinations_with_replacement(range(n),3):
            addc(e, [A], B, "E%s_%s_%s"%(e,A,B))
c = S.coeff_mu(G)
print("with (3,1)/(1,3) contamination: coefficient is exactly 1?", c==S.ONE, " #param-monomials:", len(c))
