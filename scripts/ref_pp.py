"""Independent referee check of Corollary A' / Lemma A finite statement.

n = 5 (m = 1). Field F_q, q = 2^k.
Lift R = R_s + Psi. The Psi-part of phi_e is EXACTLY an arbitrary quadratic form in
the Pluecker coordinates P_ij = a_i b_j + a_j b_i  (see referee note), so we
parametrise it directly by 55 free coefficients S[e][r] per e.

    phi_e = a_p b_q P_e + sum_{r = (ij<=cd)} S[e][r] P_ij P_cd          e = {p<q}
    G_e   = phi_e + sum_s c[e][s] Mon_s        (contamination, bidegree <= (2,2), != (2,2))
    PP    = sum_{e={p<q}} G_e * det3[(a^2, ab, b^2) on [5]\\{p,q}]

Bitsliced GF(2^k) over all (or sampled) pairs (a,b) at once.
"""
import numpy as np, itertools, random, sys, time

# ---------------- bitsliced GF(2^k) ----------------
MODP = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011}

class GF:
    def __init__(self, k):
        self.k = k; self.q = 1 << k; self.mod = MODP[k]
        red = []; cur = 1
        for _ in range(2*k-1):
            red.append(cur)
            cur <<= 1
            if (cur >> k) & 1: cur ^= self.mod
        self.red = red
        # scalar-multiplication matrices: Mc[c][l] = bitmask of i's with w^l coeff of c*w^i
        self.Mc = []
        for c in range(self.q):
            cols = []
            for i in range(k):
                v = 0
                # c * w^i
                x = c
                for _ in range(i):
                    x <<= 1
                    if (x >> k) & 1: x ^= self.mod
                cols.append(x)
            rows = [[i for i in range(k) if (cols[i] >> l) & 1] for l in range(k)]
            self.Mc.append(rows)
        # slow scalar mul table
        self.MUL = [[self._m(a, b) for b in range(self.q)] for a in range(self.q)]

    def _m(self, a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if (a >> self.k) & 1: a ^= self.mod
        return r

    def zero(self, W): return [np.zeros(W, dtype=np.uint64) for _ in range(self.k)]

    def mul(self, X, Y):
        k = self.k
        t = [None]*(2*k-1)
        for i in range(k):
            for j in range(k):
                p = X[i] & Y[j]
                t[i+j] = p if t[i+j] is None else (t[i+j] ^ p)
        Z = [None]*k
        for mdeg in range(2*k-1):
            if t[mdeg] is None: continue
            r = self.red[mdeg]
            for l in range(k):
                if (r >> l) & 1:
                    Z[l] = t[mdeg].copy() if Z[l] is None else (Z[l] ^ t[mdeg])
        W = len(X[0])
        return [np.zeros(W, dtype=np.uint64) if z is None else z for z in Z]

    def addto(self, Z, X):
        for l in range(self.k): Z[l] ^= X[l]

    def axpy(self, Z, c, X):
        """Z ^= c * X  (c a field constant)."""
        if c == 0: return
        rows = self.Mc[c]
        for l in range(self.k):
            for i in rows[l]: Z[l] ^= X[i]

    def nonzero_mask(self, X):
        m = X[0].copy()
        for l in range(1, self.k): m |= X[l]
        return m

POP = np.array([bin(i).count('1') for i in range(256)], dtype=np.uint16)
def popcount(m): return int(POP[m.view(np.uint8)].sum())

def pack(vals, k):
    """vals: uint8 array of field elements (length multiple of 64) -> k bitplanes of uint64."""
    planes = []
    for l in range(k):
        bits = ((vals >> l) & 1).astype(np.uint8)
        planes.append(np.packbits(bits, bitorder='little').view(np.uint64).copy())
    return planes

# ---------------- problem setup ----------------
N = 5
PAIRS = [(i, j) for i in range(N) for j in range(i+1, N)]   # 10
QIDX = [(r, s) for r in range(10) for s in range(r, 10)]    # 55

def build_arrays(F, avals, bvals):
    """avals,bvals: (N, M) uint8 arrays of coordinates over M sample points."""
    k = F.k
    A = [pack(avals[i], k) for i in range(N)]
    B = [pack(bvals[i], k) for i in range(N)]
    P = {}
    for (i, j) in PAIRS:
        X = F.mul(A[i], B[j]); Y = F.mul(A[j], B[i])
        P[(i, j)] = [X[l] ^ Y[l] for l in range(k)]
    A2 = [F.mul(A[i], A[i]) for i in range(N)]
    AB = [F.mul(A[i], B[i]) for i in range(N)]
    B2 = [F.mul(B[i], B[i]) for i in range(N)]
    # det3 on each 3-subset L (= complement of a pair e)
    D = {}
    for e in PAIRS:
        L = [i for i in range(N) if i not in e]
        acc = F.zero(len(A[0][0]))
        for perm in itertools.permutations(L):
            i, j, r = perm
            t = F.mul(F.mul(A2[i], AB[j]), B2[r])
            F.addto(acc, t)
        D[e] = acc
    sorted_e = {}
    for e in PAIRS:
        p, q = e
        sorted_e[e] = F.mul(F.mul(A[p], B[q]), P[e])
    Plist = [P[e] for e in PAIRS]
    QP = [F.mul(Plist[r], Plist[s]) for (r, s) in QIDX]
    return dict(A=A, B=B, P=P, Plist=Plist, A2=A2, AB=AB, B2=B2, D=D,
                sorted_e=sorted_e, QP=QP, W=len(A[0][0]))

def monomial_basis(rnd, nmon):
    """random monomials a^alpha b^beta with |alpha|,|beta| <= 2, != (2,2)."""
    out = set()
    while len(out) < nmon:
        da = rnd.randrange(3); db = rnd.randrange(3)
        if (da, db) == (2, 2): continue
        ea = [0]*N; eb = [0]*N
        for _ in range(da): ea[rnd.randrange(N)] += 1
        for _ in range(db): eb[rnd.randrange(N)] += 1
        out.add((tuple(ea), tuple(eb)))
    return sorted(out)

def build_monomials(F, ctx, mons):
    ones = [np.full(ctx['W'], np.uint64(0xFFFFFFFFFFFFFFFF), dtype=np.uint64)] + \
           [np.zeros(ctx['W'], dtype=np.uint64) for _ in range(F.k-1)]
    out = []
    for (ea, eb) in mons:
        cur = [x.copy() for x in ones]
        for i in range(N):
            for _ in range(ea[i]): cur = F.mul(cur, ctx['A'][i])
            for _ in range(eb[i]): cur = F.mul(cur, ctx['B'][i])
        out.append(cur)
    return out

def eval_PP(F, ctx, MON, S, C):
    """S[e_index][r] field consts (55), C[e_index][s] field consts."""
    W = ctx['W']
    PP = F.zero(W)
    for ei, e in enumerate(PAIRS):
        G = [x.copy() for x in ctx['sorted_e'][e]]
        Se = S[ei]
        for r in range(len(QIDX)):
            c = Se[r]
            if c: F.axpy(G, c, ctx['QP'][r])
        Ce = C[ei]
        for s in range(len(MON)):
            c = Ce[s]
            if c: F.axpy(G, c, MON[s])
        F.addto(PP, F.mul(G, ctx['D'][e]))
    return PP

# ---------------- slow reference (single point) ----------------
def slow_PP(F, a, b, S, C, mons):
    MUL = F.MUL
    def mul(x, y): return MUL[x][y]
    P = {}
    for (i, j) in PAIRS:
        P[(i, j)] = mul(a[i], b[j]) ^ mul(a[j], b[i])
    Pl = [P[e] for e in PAIRS]
    A2 = [mul(a[i], a[i]) for i in range(N)]
    AB = [mul(a[i], b[i]) for i in range(N)]
    B2 = [mul(b[i], b[i]) for i in range(N)]
    tot = 0
    for ei, e in enumerate(PAIRS):
        p, q = e
        g = mul(mul(a[p], b[q]), P[e])
        for r, (u, v) in enumerate(QIDX):
            if S[ei][r]: g ^= mul(S[ei][r], mul(Pl[u], Pl[v]))
        for s, (ea, eb) in enumerate(mons):
            if C[ei][s]:
                t = 1
                for i in range(N):
                    for _ in range(ea[i]): t = mul(t, a[i])
                    for _ in range(eb[i]): t = mul(t, b[i])
                g ^= mul(C[ei][s], t)
        L = [i for i in range(N) if i not in e]
        d3 = 0
        for perm in itertools.permutations(L):
            i, j, r = perm
            d3 ^= mul(mul(A2[i], AB[j]), B2[r])
        tot ^= mul(g, d3)
    return tot
