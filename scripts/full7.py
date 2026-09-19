# EXHAUSTIVE formal verification of Lemma A for n=5: every Psi_{ij}[e,cd] and every
# contamination coefficient is a distinct formal indeterminate over F_2.  No sampling.
import itertools
n=7; m=(n-3)//2
MUa=[2,0]+[1]*(n-2); MUb=[0,2]+[1]*(n-2)
Z=tuple([0]*n)
def ok(mon):
    ea,eb,_=mon
    return all(x<=y for x,y in zip(ea,MUa)) and all(x<=y for x,y in zip(eb,MUb))
def padd(p,q): return set(p)^set(q)
def pmul(p,q):
    r=set()
    for (a1,b1,s1) in p:
        for (a2,b2,s2) in q:
            if s1 & s2: continue
            mon=(tuple(x+y for x,y in zip(a1,a2)),tuple(x+y for x,y in zip(b1,b2)),s1|s2)
            if ok(mon): r^={mon}
    return r
def va(i):
    e=[0]*n; e[i]=1; return {(tuple(e),Z,frozenset())}
def vb(i):
    e=[0]*n; e[i]=1; return {(Z,tuple(e),frozenset())}
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]
P={(c,d): padd(pmul(va(c),vb(d)),pmul(va(d),vb(c))) for (c,d) in pairs}
PP={(ij,cd): pmul(P[ij],P[cd]) for ij in pairs for cd in pairs}
# all exponent vectors of total degree d in n vars
def exps(d):
    out=[]
    for c in itertools.combinations_with_replacement(range(n),d):
        e=[0]*n
        for i in c: e[i]+=1
        out.append(tuple(e))
    return out
EX={d:exps(d) for d in (0,1,2)}
nsym=0
G={}
for e in pairs:
    k,l=e
    g=pmul(pmul(va(k),vb(l)),P[e])
    for ij in pairs:                       # FULL Psi: every (ij, cd) coefficient formal
        for cd in pairs:
            sym=frozenset([("psi",e,ij,cd)]); nsym+=1
            g=padd(g,{(a,b,s|sym) for (a,b,s) in PP[(ij,cd)]})
    for da in (0,1,2):                     # FULL contamination basis, bidegree <=(2,2), !=(2,2)
        for db in (0,1,2):
            if (da,db)==(2,2): continue
            for ea in EX[da]:
                for eb in EX[db]:
                    mon=(ea,eb,frozenset([("cont",e,ea,eb)])); nsym+=1
                    if ok(mon): g=padd(g,{mon})
    G[e]=g
print("total formal parameters:",nsym)
def matchings(idx):
    if not idx: yield []; return
    a=idx[0]
    for t in range(1,len(idx)):
        b=idx[t]; rest=idx[1:t]+idx[t+1:]
        for mm in matchings(rest): yield [(a,b)]+mm
total=set()
for trip in itertools.permutations(range(n),3):
    i,j,r=trip
    border=pmul(pmul(pmul(va(i),va(i)),pmul(va(j),vb(j))),pmul(vb(r),vb(r)))
    if not border: continue
    rest=[x for x in range(n) if x not in trip]
    for M in matchings(rest):
        term=border
        for e in M:
            term=pmul(term,G[e])
            if not term: break
        total=padd(total,term)
coef=sorted(s for (a,b,s) in total if a==tuple(MUa) and b==tuple(MUb))
print("coef(mu) monomial count:",len(coef),"  exactly {1}?",coef==[frozenset()])
for c in coef[:5]:
    if c: print("  NONCONSTANT:",sorted(c))
