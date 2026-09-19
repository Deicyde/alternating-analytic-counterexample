#!/usr/bin/env python3
"""Check the PER-GROUP claim of Lemma A's proof (stronger than the aggregate):
for every (j, M, nonempty M', parameter assignment e->((i,j),(c,d))), the number of
orientation tuples producing the target multilinear monomial is EVEN, and the
simultaneous flip is a fixed-point-free involution on that set.
Also checks the M'=empty count is (2m+1)!!."""
import sys, itertools
from collections import Counter

n = int(sys.argv[1]); m = (n - 3) // 2
pairs = [(c, d) for c in range(n) for d in range(c + 1, n)]

def matchings(idx):
    if not idx:
        yield []; return
    a = idx[0]
    for t in range(1, len(idx)):
        b = idx[t]; rest = idx[1:t] + idx[t + 1:]
        for mm in matchings(rest): yield [(a, b)] + mm

def orient_mono(ij, cd, bits):
    """bits=(s,t); monomial as (sorted a-idx tuple, sorted b-idx tuple)."""
    x, y = (ij[0], ij[1]) if bits[0] == 0 else (ij[1], ij[0])
    z, w = (cd[0], cd[1]) if bits[1] == 0 else (cd[1], cd[0])
    return (tuple(sorted((x, z))), tuple(sorted((y, w))))

bad = 0; groups = 0; nonempty_odd = 0
for j in range(2, n):
    J = [x for x in range(n) if x not in (0, 1, j)]
    for M in matchings(J):
        for size in range(1, len(M) + 1):
            for Mp in itertools.combinations(range(len(M)), size):
                target_idx = sorted(sum((list(M[t]) for t in Mp), []))
                rest_ok = True   # M\M' positions must give a_p a_q b_p b_q (only squarefree option)
                for assign in itertools.product(itertools.product(pairs, pairs), repeat=size):
                    groups += 1
                    valid = []
                    for bits in itertools.product([(0,0),(0,1),(1,0),(1,1)], repeat=size):
                        A = []; B = []
                        ok = True
                        for t in range(size):
                            (ij, cd) = assign[t]
                            am, bm = orient_mono(ij, cd, bits[t])
                            if am[0] == am[1] or bm[0] == bm[1]: ok = False; break  # not squarefree
                            A += list(am); B += list(bm)
                        if ok and sorted(A) == target_idx and sorted(B) == target_idx:
                            valid.append(bits)
                    if len(valid) % 2:
                        nonempty_odd += 1
                    # flip check
                    S = set(valid)
                    for bits in valid:
                        fl = tuple((1 - b0, 1 - b1) for (b0, b1) in bits)
                        if fl not in S: bad += 1
                        if fl == bits: bad += 1
print("n=%d  groups examined=%d  flip-violations=%d  odd nonempty groups=%d"
      % (n, groups, bad, nonempty_odd))

# M' = empty count
cnt = sum(1 for j in range(2, n) for M in matchings([x for x in range(n) if x not in (0,1,j)]))
dfac = 1
for k in range(1, 2*m+2, 2): dfac *= k
print("  M'=empty contributions: %d ; (2m+1)!! = %d ; parity %d" % (cnt, dfac, cnt % 2))
