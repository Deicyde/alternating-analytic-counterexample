import os
"""EXACT decision (not heuristic) of: does there exist a lift + contamination whose
PP vanishes identically on F_q^5 x F_q^5 ?

PP(a,b) = PP0(a,b) + sum_j theta_j * B_j(a,b)  is AFFINE-LINEAR in the full parameter
vector theta, where the parameters are
   - 55 per e : the arbitrary quadratic form in the Pluecker coords P_ij  (= the Psi part,
                and this is exactly the general (2,2)-part of any lift)
   - 216 per e: ALL monomials a^alpha b^beta with |alpha|,|beta| <= 2, (|alpha|,|beta|) != (2,2)
                (= the completely general contamination)
=> 2710 F_q parameters.  "Zero good pairs" <=> PP0 lies in the F_q-span of {B_j} inside
F_q^{T} for T = all sample points.  Decide by F_2 Gaussian elimination on F_2^{k*T}.
"""
import numpy as np, random, itertools, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_pp import *

k = int(sys.argv[1]); T = int(sys.argv[2]); SEED = int(sys.argv[3])
F = GF(k); q = F.q
assert T % 64 == 0
rs = np.random.RandomState(SEED)
if q**(2*N) <= T:
    M = q**(2*N)
    idx = np.arange(M, dtype=np.int64); ia = idx // (q**N); ib = idx % (q**N)
    avals = np.array([((ia // q**i) % q).astype(np.uint8) for i in range(N)])
    bvals = np.array([((ib // q**i) % q).astype(np.uint8) for i in range(N)])
    T = M; ALL = True
else:
    avals = rs.randint(0, q, size=(N, T)).astype(np.uint8)
    bvals = rs.randint(0, q, size=(N, T)).astype(np.uint8)
    ALL = False
ctx = build_arrays(F, avals, bvals)

# FULL contamination basis
amons = [tuple(e) for d in range(3) for e in
         set(tuple(sorted_c) for sorted_c in
             [tuple(np.bincount(c, minlength=N)) for c in itertools.combinations_with_replacement(range(N), d)])]
def degmons(d):
    out = []
    for c in itertools.combinations_with_replacement(range(N), d):
        e = [0]*N
        for i in c: e[i] += 1
        out.append(tuple(e))
    return out
AM = degmons(0) + degmons(1) + degmons(2)
BM = AM
mons = [(am, bm) for am in AM for bm in BM
        if not (sum(am) == 2 and sum(bm) == 2)]
print(f"q={q} T={T} allpoints={ALL} contamination monomials/e = {len(mons)}", flush=True)
MON = build_monomials(F, ctx, mons)

BAS = []
for ei, e in enumerate(PAIRS):
    for r in range(len(QIDX)): BAS.append(F.mul(ctx['QP'][r], ctx['D'][e]))
    for s in range(len(mons)): BAS.append(F.mul(MON[s], ctx['D'][e]))
PP0 = F.zero(ctx['W'])
for e in PAIRS: F.addto(PP0, F.mul(ctx['sorted_e'][e], ctx['D'][e]))
print(f"parameters over F_q: {len(BAS)}  ->  F_2 unknowns: {len(BAS)*k}", flush=True)

def tovec(X):
    b = b''.join(X[l].tobytes() for l in range(k))
    return int.from_bytes(b, 'little')

t0 = time.time()
basis = {}
def add(v):
    while v:
        p = v.bit_length() - 1
        if p in basis: v ^= basis[p]
        else: basis[p] = v; return True
    return False

for j, Bj in enumerate(BAS):
    for c in range(1, q):
        Z = F.zero(ctx['W']); F.axpy(Z, c, Bj)
        add(tovec(Z))
rank = len(basis)
print(f"rank of parameter span = {rank}  (ambient {k*T})  elim_time={time.time()-t0:.0f}s", flush=True)

v = tovec(PP0)
red = v
while red:
    p = red.bit_length() - 1
    if p in basis: red ^= basis[p]
    else: break
print("PP0 in span(parameters)?", "YES -> a lift with PP == 0 on these points EXISTS"
      if red == 0 else "NO  -> NO lift/contamination can make PP vanish on these points")
print(f"  (rank {rank} < ambient {k*T}: test is non-vacuous = {rank < k*T})")
print(f"total time {time.time()-t0:.0f}s", flush=True)
