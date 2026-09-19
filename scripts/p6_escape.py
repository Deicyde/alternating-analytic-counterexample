# P6: the sorted "Phillips" lift for the BIG target ell^inf(NxN) applied to
# f = id, g = m_z (z_j = j mod 2), m = W, x = 1, y = z.
# P(f,g)(m)(x,y)_{pq} = sum_{i<j} m(f e_i, g e_j)_{pq} (x_i y_j + x_j y_i)
#                     = z_q (x_p y_q + x_q y_p)   for p<q   (entrywise, char 2)
N = 40
z = [j % 2 for j in range(N)]
x = [1]*N
y = z[:]
M = [[0]*N for _ in range(N)]
for p in range(N):
    for q in range(p+1, N):
        v = (z[q]*(x[p]*y[q] + x[q]*y[p])) % 2
        M[p][q] = v; M[q][p] = v
# submatrix: rows = even indices, cols = odd indices
def det2(A):
    A = [r[:] for r in A]; n = len(A); d = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c]), None)
        if piv is None: return 0
        A[c], A[piv] = A[piv], A[c]
        for r in range(c+1, n):
            if A[r][c]:
                A[r] = [(u+v) % 2 for u, v in zip(A[r], A[c])]
    return 1
for K in (3, 5, 10, 20):
    rows = [2*s for s in range(K)]; cols = [2*t+1 for t in range(K)]
    S = [[M[r][c] for c in cols] for r in rows]
    print("K=%2d  |det| of %dx%d submatrix over F_2 = %d" % (K, K, K, det2(S)))
print("upper-left 8x8 of M:")
for r in range(8): print("   ", M[r][:8])
