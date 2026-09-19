# Section-4-faithful check.
# Index set {0,...,n}: index 0 plays the role of the EARLIER blocks (a', b'), I = {1..n} is the current block.
# Phi is a genuine 4-linear F-valued map on k^{n+1} with Phi(a,a;x,y) = W(ax,ay):
#     Phi = Phi_sorted + Delta,  Delta alternating in (a,b) with arbitrary alternating-in-(x,y) F-valued coefficients.
# G := Phi(a'+a_t, b'+b_t ; a'+a_t, b'+b_t)|_{IxI}   (this is exactly G_t of Sec 4)
# PP := sum over ordered triples (i,j,r) in I and matchings of I minus {i,j,r} of  a_i^2 (a_j b_j) b_r^2 * prod G_e
# Claim (Lemma A + Sec 4 step 4): coefficient of mu = a_1^2 b_2^2 prod_{i>=3} a_i b_i  equals 1,
# and NO monomial mu * a_0^i b_0^j with (i,j) != (0,0) survives either.
import random, sys, itertools

n = int(sys.argv[1]); trials = int(sys.argv[2]); dens = float(sys.argv[3]) if len(sys.argv) > 3 else 0.25
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
m = (n - 3) // 2
FULL = list(range(n + 1))          # 0 = prior blocks, 1..n = current block I
NV = n + 1
# mu bounds: index 0 unconstrained up to 2; indices 1..n as in Lemma A
MUa = [2] + [2, 0] + [1] * (n - 2)
MUb = [2] + [0, 2] + [1] * (n - 2)

def ok(mon):
    ea, eb = mon
    return all(x <= y for x, y in zip(ea, MUa)) and all(x <= y for x, y in zip(eb, MUb))

def padd(p, q): return set(p) ^ set(q)

def pmul(p, q):
    r = set()
    for (ea1, eb1) in p:
        for (ea2, eb2) in q:
            mon = (tuple(x + y for x, y in zip(ea1, ea2)), tuple(x + y for x, y in zip(eb1, eb2)))
            if ok(mon): r ^= {mon}
    return r

Z = tuple([0] * NV)
def va(i):
    e = [0] * NV; e[i] = 1; return {(tuple(e), Z)}
def vb(i):
    e = [0] * NV; e[i] = 1; return {(Z, tuple(e))}

pairs = [(c, d) for c in FULL for d in FULL if c < d]

def rnd_alt_F(rnd):
    """random F-valued alternating-in-(x,y) bilinear form: dict (p<q) -> list of (c<d) used"""
    out = {}
    for (p, q) in pairs:
        out[(p, q)] = [cd for cd in pairs if rnd.random() < dens]
    return out

rnd = random.Random(seed)
mu = (tuple(MUa[:1] and [0] + MUa[1:]), tuple([0] + MUb[1:]))  # a_0,b_0 exponent 0

for t in range(trials):
    # Delta[(i,j)] = alternating-in-(x,y) F-valued form, coefficient of p_ij(a,b)
    Delta = {}
    if t > 0:
        for ij in pairs:
            Delta[ij] = rnd_alt_F(rnd)

    # --- build G_{pq}, p<q in I, as a polynomial in a_0..a_n, b_0..b_n ---
    # W(x,y)_{cd} with x=a, y=b (both full vectors): p_cd = a_c b_d + a_d b_c
    Pcd = {(c, d): padd(pmul(va(c), vb(d)), pmul(va(d), vb(c))) for (c, d) in pairs}
    G = {}
    for (p, q) in [(p, q) for p in range(1, n + 1) for q in range(1, n + 1) if p < q]:
        # sorted part: a_p b_q * (x_p y_q + x_q y_p) with x=a, y=b  ->  a_p b_q * p_pq
        g = pmul(pmul(va(p), vb(q)), Pcd[(p, q)])
        if t > 0:
            for ij in pairs:
                for cd in Delta[ij][(p, q)]:
                    g = padd(g, pmul(Pcd[ij], Pcd[cd]))
        G[(p, q)] = g

    def Ge(e):
        p, q = min(e), max(e); return G[(p, q)]

    def matchings(idx):
        if not idx: yield []; return
        a0 = idx[0]
        for tt in range(1, len(idx)):
            b0 = idx[tt]; rest = idx[1:tt] + idx[tt + 1:]
            for mm in matchings(rest): yield [(a0, b0)] + mm

    total = set()
    I = list(range(1, n + 1))
    for trip in itertools.permutations(I, 3):
        i, j, r = trip
        border = pmul(pmul(pmul(va(i), va(i)), pmul(va(j), vb(j))), pmul(vb(r), vb(r)))
        if not border: continue
        rest = [x for x in I if x not in trip]
        for M in matchings(rest):
            term = border
            for e in M:
                term = pmul(term, Ge(e))
                if not term: break
            total = padd(total, term)

    # coefficient of mu (a_0,b_0 exponents zero) and of mu*a_0^i b_0^j
    core_a = tuple([0] + MUa[1:]); core_b = tuple([0] + MUb[1:])
    hits = {}
    for (ea, eb) in total:
        if ea[1:] == core_a[1:] and eb[1:] == core_b[1:]:
            hits[(ea[0], eb[0])] = 1
    print("trial", t, "(sorted only)" if t == 0 else "(random Delta)",
          "coeff of mu:", hits.get((0, 0), 0),
          "| other a_0^i b_0^j * mu terms:", sorted(k for k in hits if k != (0, 0)), flush=True)
