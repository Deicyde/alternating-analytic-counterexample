import sys
from halfsel import subspaces, plucker
def gen(n,r,fname):
    out=["(set-logic QF_UF)"]
    def s(i,j,k,l):
        if k>l: k,l=l,k
        return f"s_{i}_{j}_{k}_{l}"
    for i in range(n):
        for j in range(i+1,n):
            for k in range(n):
                for l in range(k,n):
                    out.append(f"(declare-const {s(i,j,k,l)} Bool)")
    for idx,(x,y) in enumerate(subspaces(n)):
        pl=plucker(n,x,y)
        for k in range(n):
            for q in range(r): out.append(f"(declare-const a_{idx}_{k}_{q} Bool)")
        for q in range(r):
            for l in range(n): out.append(f"(declare-const b_{idx}_{q}_{l} Bool)")
        for k in range(n):
            for l in range(n):
                terms=[s(i,j,k,l) for (i,j) in pl]
                const = sum(1 for (i,j) in pl if (i,j)==(k,l))%2
                lhs = "false" if not terms else (terms[0] if len(terms)==1 else "(xor "+" ".join(terms)+")")
                if const: lhs=f"(not {lhs})"
                prods=[f"(and a_{idx}_{k}_{q} b_{idx}_{q}_{l})" for q in range(r)]
                rhs = prods[0] if r==1 else "(xor "+" ".join(prods)+")"
                out.append(f"(assert (= {lhs} {rhs}))")
    out.append("(check-sat)")
    open(fname,"w").write("\n".join(out)+"\n")
if __name__=="__main__":
    n=int(sys.argv[1]); r=int(sys.argv[2]); gen(n,r,f"hs_{n}_{r}.smt2")
