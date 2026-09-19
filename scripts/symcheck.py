# Independent check of Lemma A with Psi entries as FORMAL indeterminates (sampled subset),
# plus formal contamination with indeterminate coefficients.
import random, sys, itertools
n=int(sys.argv[1]); nsym=int(sys.argv[2]); ncont=int(sys.argv[3]); seed=int(sys.argv[4])
m=(n-3)//2
MUa=[2,0]+[1]*(n-2); MUb=[0,2]+[1]*(n-2)
def ok(mon):
    ea,eb,_=mon
    return all(x<=y for x,y in zip(ea,MUa)) and all(x<=y for x,y in zip(eb,MUb))
Z=tuple([0]*n)
def padd(p,q): return set(p)^set(q)
def pmul(p,q):
    r=set()
    for (a1,b1,s1) in p:
        for (a2,b2,s2) in q:
            if s1 & s2: continue          # symbols are degree<=1; shared symbol impossible here
            mon=(tuple(x+y for x,y in zip(a1,a2)),tuple(x+y for x,y in zip(b1,b2)),s1|s2)
            if ok(mon): r^={mon}
    return r
def va(i):
    e=[0]*n; e[i]=1; return {(tuple(e),Z,frozenset())}
def vb(i):
    e=[0]*n; e[i]=1; return {(Z,tuple(e),frozenset())}
pairs=[(c,d) for c in range(n) for d in range(c+1,n)]
P={(c,d): padd(pmul(va(c),vb(d)),pmul(va(d),vb(c))) for (c,d) in pairs}
PP={}
def pp(ij,cd):
    if (ij,cd) not in PP: PP[(ij,cd)]=pmul(P[ij],P[cd])
    return PP[(ij,cd)]
rnd=random.Random(seed)
G={}
for e in pairs:
    k,l=e
    g=pmul(pmul(va(k),vb(l)),P[e])
    # sampled Psi terms with formal symbol coefficients
    for _ in range(nsym):
        ij=rnd.choice(pairs); cd=rnd.choice(pairs)
        sym=frozenset([("psi",e,ij,cd)])
        term={(a,b,s|sym) for (a,b,s) in pp(ij,cd)}
        g=padd(g,{t for t in term if ok(t)})
    # formal contamination: random monomials of bidegree <=(2,2), !=(2,2), with formal coefficients
    for c in range(ncont):
        da=rnd.randrange(3); db=rnd.randrange(3)
        if (da,db)==(2,2): continue
        ea=[0]*n; eb=[0]*n
        for _ in range(da): ea[rnd.randrange(n)]+=1
        for _ in range(db): eb[rnd.randrange(n)]+=1
        mon=(tuple(ea),tuple(eb),frozenset([("cont",e,c)]))
        if ok(mon): g=padd(g,{mon})
    G[e]=g
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
print("n=",n,"num Psi symbols/edge=",nsym,"cont/edge=",ncont)
print("coefficient of mu as polynomial in the formal parameters:")
print("  number of monomials:",len(coef))
print("  is it exactly {1}? ", coef==[frozenset()])
if coef!=[frozenset()]:
    for c in coef[:10]: print("   ",sorted(c))
