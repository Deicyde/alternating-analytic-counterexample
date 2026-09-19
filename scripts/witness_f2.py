import os
"""Over F_2, n=5: solve for an explicit lift+contamination with PP identically 0 on
ALL 1024 pairs, then verify it with the independent slow reference."""
import numpy as np, itertools, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ref_pp import *

F = GF(1); q = 2
M = q**(2*N)
idx = np.arange(M, dtype=np.int64); ia = idx // (q**N); ib = idx % (q**N)
avals = np.array([((ia // q**i) % q).astype(np.uint8) for i in range(N)])
bvals = np.array([((ib // q**i) % q).astype(np.uint8) for i in range(N)])
ctx = build_arrays(F, avals, bvals)

def degmons(d):
    out = []
    for c in itertools.combinations_with_replacement(range(N), d):
        e = [0]*N
        for i in c: e[i] += 1
        out.append(tuple(e))
    return out
AM = degmons(0)+degmons(1)+degmons(2)
mons = [(x, y) for x in AM for y in AM if not (sum(x) == 2 and sum(y) == 2)]
MON = build_monomials(F, ctx, mons)
NS, NC = len(QIDX), len(mons)

cols = []          # (param index -> (ei, kind, r))
BAS = []
for ei, e in enumerate(PAIRS):
    for r in range(NS): BAS.append(F.mul(ctx['QP'][r], ctx['D'][e])); cols.append((ei, 'S', r))
    for s in range(NC): BAS.append(F.mul(MON[s], ctx['D'][e])); cols.append((ei, 'C', s))
PP0 = F.zero(ctx['W'])
for e in PAIRS: F.addto(PP0, F.mul(ctx['sorted_e'][e], ctx['D'][e]))
def tovec(X): return int.from_bytes(X[0].tobytes(), 'little')

basis = {}
for j, Bj in enumerate(BAS):
    v, tr = tovec(Bj), 1 << j
    while v:
        p = v.bit_length()-1
        if p in basis:
            bv, bt = basis[p]; v ^= bv; tr ^= bt
        else:
            basis[p] = (v, tr); break

v, tr = tovec(PP0), 0
while v:
    p = v.bit_length()-1
    if p not in basis: break
    bv, bt = basis[p]; v ^= bv; tr ^= bt
if v != 0:
    print("no solution"); sys.exit()
theta = [(tr >> j) & 1 for j in range(len(BAS))]
print("solution found; nonzero params:", sum(theta))

S = [[0]*NS for _ in PAIRS]; C = [[0]*NC for _ in PAIRS]
for j, t in enumerate(theta):
    if t:
        ei, kind, r = cols[j]
        (S if kind == 'S' else C)[ei][r] = 1

bad = 0
for j in range(M):
    a = [int(avals[i][j]) for i in range(N)]
    b = [int(bvals[i][j]) for i in range(N)]
    if slow_PP(F, a, b, S, C, mons) != 0: bad += 1
print(f"INDEPENDENT slow-reference check over all {M} pairs: nonzero PP at {bad} pairs")
print("  => over F_2 there IS a lift+contamination with PP identically zero" if bad == 0 else "  => witness failed")
