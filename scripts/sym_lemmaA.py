#!/usr/bin/env python3
"""Independent SYMBOLIC check of Lemma A.

Different code path from topcoef7.py: coefficients of the (a,b)-monomials are
themselves polynomials over F_2 in free parameters  Y[e,ij,cd] ( = Psi_ij[e,cd] )
and C[e,mon] (contamination), represented as sets of parameter-monomials.
A symbolic result of exactly {1} means NO choice of Psi / contamination over ANY
commutative ring of characteristic 2 can change the coefficient of mu.

usage: sym_lemmaA.py n [contamination_mode]   mode in {sym, rand, none}
"""
import sys, itertools, random
from collections import defaultdict

n = int(sys.argv[1])
mode = sys.argv[2] if len(sys.argv) > 2 else "sym"
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
m = (n - 3) // 2
MUa = [2, 0] + [1] * (n - 2)
MUb = [0, 2] + [1] * (n - 2)
rnd = random.Random(seed)

# ---------- coefficient ring: F_2[params] as set of sorted tuples of param ids
ZERO = frozenset()
ONE = frozenset({()})
def cadd(s, t):
    return frozenset(s ^ t)
def cmul(s, t):
    out = set()
    for u in s:
        for v in t:
            out ^= {tuple(sorted(u + v))}
    return frozenset(out)
def cvar(name):
    return frozenset({(name,)})

# ---------- polynomials in a,b with those coefficients
def div_mu(ea, eb):
    return all(x <= y for x, y in zip(ea, MUa)) and all(x <= y for x, y in zip(eb, MUb))

def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        w = cadd(r.get(k, ZERO), v)
        if w: r[k] = w
        elif k in r: del r[k]
    return r

def pmul(p, q):
    r = {}
    for (ea1, eb1), c1 in p.items():
        for (ea2, eb2), c2 in q.items():
            ea = tuple(x + y for x, y in zip(ea1, ea2))
            eb = tuple(x + y for x, y in zip(eb1, eb2))
            if not div_mu(ea, eb):     # safe: exponents only grow
                continue
            c = cmul(c1, c2)
            if not c: continue
            k = (ea, eb)
            w = cadd(r.get(k, ZERO), c)
            if w: r[k] = w
            elif k in r: del r[k]
    return r

Z = tuple([0] * n)
def mono(alist, blist, coef=ONE):
    ea = [0] * n; eb = [0] * n
    for i in alist: ea[i] += 1
    for i in blist: eb[i] += 1
    return {(tuple(ea), tuple(eb)): coef}

pairs = [(c, d) for c in range(n) for d in range(c + 1, n)]
# p_cd = a_c b_d + a_d b_c
P = {e: padd(mono([e[0]], [e[1]]), mono([e[1]], [e[0]])) for e in pairs}
PP = {}
for ij in pairs:
    for cd in pairs:
        PP[(ij, cd)] = pmul(P[ij], P[cd])   # cancellation of equal monomials happens here

# contamination basis: bidegree (da,db), da,db <= 2, (da,db) != (2,2)
def contamination(e):
    out = {}
    for da in range(3):
        for db in range(3):
            if (da, db) == (2, 2): continue
            for A in itertools.combinations_with_replacement(range(n), da):
                for B in itertools.combinations_with_replacement(range(n), db):
                    ea = [0] * n; eb = [0] * n
                    for i in A: ea[i] += 1
                    for i in B: eb[i] += 1
                    if not div_mu(tuple(ea), tuple(eb)):  # cannot ever reach mu
                        continue
                    if mode == "sym":
                        c = cvar("C%s_%s_%s" % (e, A, B))
                    elif mode == "rand":
                        if rnd.random() < 0.5: continue
                        c = ONE
                    else:
                        continue
                    out = padd(out, {(tuple(ea), tuple(eb)): c})
    return out

def build_G(psi_mode="sym", psi_filter=None, psi_val=None):
    G = {}
    for e in pairs:
        p, q = e
        g = pmul(mono([p], [q]), P[e])        # sorted part a_p b_q * p_pq
        for ij in pairs:
            for cd in pairs:
                if psi_filter and not psi_filter(e, ij, cd): continue
                if psi_mode == "sym":
                    c = cvar("Y%s_%s_%s" % (e, ij, cd))
                else:
                    if not psi_val(e, ij, cd): continue
                    c = ONE
                g = padd(g, {k: cmul(v, c) for k, v in PP[(ij, cd)].items()})
        if mode != "none":
            g = padd(g, contamination(e))
        G[e] = g
    return G

def matchings(idx):
    if not idx:
        yield []; return
    a = idx[0]
    for t in range(1, len(idx)):
        b = idx[t]; rest = idx[1:t] + idx[t + 1:]
        for mm in matchings(rest):
            yield [(a, b)] + mm

def coeff_mu(G, report=False):
    mu = (tuple(MUa), tuple(MUb))
    total = ZERO
    used = []
    for (i, j, r) in itertools.permutations(range(n), 3):
        border = mono([i, i, j], [j, r, r])
        if not all(div_mu(*k) for k in border): continue
        rest = [x for x in range(n) if x not in (i, j, r)]
        for M in matchings(rest):
            term = border
            for e in M:
                term = pmul(term, G[e])
                if not term: break
            c = term.get(mu, ZERO)
            if c:
                used.append(((i, j, r), tuple(M), len(c)))
                total = cadd(total, c)
    if report:
        print("  surviving (i,j,r):", sorted({u[0] for u in used}))
        print("  #(triple,matching) pairs contributing:", len(used))
    return total

if __name__ == "__main__":
    print("n=%d m=%d  contamination=%s  (fully symbolic Psi: %d params)"
          % (n, m, mode, len(pairs) ** 3))
    G = build_G("sym")
    c = coeff_mu(G, report=True)
    print("  symbolic coefficient of mu =", "1" if c == ONE else sorted(c)[:12], " (is exactly 1:", c == ONE, ")")
    print("  predicted (2m+1)!! =", eval("*".join(str(k) for k in range(1, 2 * m + 2, 2))) if m >= 0 else 1)
