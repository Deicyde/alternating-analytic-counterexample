# The analytic case fails in characteristic 2: a counterexample

Date: 2026-09-19. Status: **AI-refereed only (no human expert review); the Lean development is machine-checked — see the
repository README.** Seven independent adversarial AI referees (one per section, one "does it prove too much", one global)
plus an adjudicator found no mathematical error; every gap they listed was editorial and is incorporated below. The
border form of the finite identity (Lemma A, §2) was verified as a polynomial identity with all free parameters formal
(`scripts/full5.py`: 3160 parameters at n = 5; `scripts/full7.py`: 20013 at n = 7; `scripts/sym_lemmaA.py`: n = 9). The
simplified identity of §2′ — the one the Lean proof uses — is checked numerically (`scripts/nobord.py`) and proved in Lean
(`AltCounter/Balanced.lean`, `coeff_bal_prod_matching`).

## 0. Statement

Let `k` be a complete, nontrivially valued non-archimedean field with

* `char k = 2`,
* `k` **not spherically complete**,
* infinite residue field.

Example: the completion of an algebraic closure of `F_2((t))`: value group `ℚ` (dense), residue field `F̄_2`. It is
separable as a metric space, and a complete non-archimedean field that is separable and densely valued is never
spherically complete (the same classical argument that shows `ℂ_p` is not spherically complete; see e.g. Schikhof,
*Ultrametric Calculus*, §20).

Let `E = ℓ^∞(ℕ,k)` with the sup norm, `W(x,y) := x⊗y + y⊗x ∈ ℓ^∞(ℕ×ℕ,k)` (`W(x,y)_{pq} = x_p y_q + x_q y_p`), and let
`F ⊆ ℓ^∞(ℕ×ℕ,k)` be the closed linear span of `{W(x,y) : x,y ∈ E}` (a Banach space).

> **Theorem.** The continuous homogeneous quadratic map
> `Q : L(E,E) → L(E[⋀^Fin 2]→L[k] F, E[⋀^Fin 2]→L[k] F)`, `Q(f)(m) = m∘(f,f)` (Mathlib: `compContinuousLinearMapCLM`),
> is not analytic at any point of `L(E,E)`. (Lean: at `0`; the reduction to an arbitrary base point is §1, on paper.)

Consequences.

* The theorem `contDiff_compContinuousLinearMapCLM {n : ℕ∞}` of PR #43548 is true as stated; what the counterexample
  refutes is its would-be extension to `n : WithTop ℕ∞` (i.e. `n = ω`): Mathlib's `ContDiff 𝕜 ω f` implies `AnalyticAt`
  unconditionally (`ContDiffAt.analyticAt`). So **the restriction `n : ℕ∞` is sharp**; some hypothesis such as
  `((Nat.card ι)! : 𝕜) ≠ 0` (Gouëzel, #43338), a t-orthogonal base, finite dimension, … is needed for `ω`.
* Every index type with `|ι| ≥ 2` is covered in characteristic 2: `m ↦ m∧t` (wedge with the coordinate of an extra
  factor `k`) is a bounded linear embedding `Alt²(E,F) → Alt³(E⊕k,F)` with bounded left inverse (evaluate the last slot
  at `(0,1)`), and `Q₂(f) = r ∘ Q₃(f⊕1) ∘ j`; iterate.
* Bundle level (hypothetical instance; Mathlib has only the *topological* alternating bundle,
  `Topology/VectorBundle/ContinuousAlternatingMap.lean`, whose coordinate change is
  `(e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b)`): take `B = GL(E)`, open in the
  Banach algebra `L(E,E)` (`E` complete), the trivial bundle `B × E` with trivialisations `id` and `(b,v) ↦ (b, b v)`.
  All four coordinate changes (`b ↦ b`, `b ↦ b⁻¹`, identities) are analytic (Neumann series), so this is a `C^ω` vector
  bundle; with trivial coefficient bundle `F` the induced coordinate change on alternating 2-forms is
  `b ↦ compContinuousLinearMapCLM` of `b^{±1}`, i.e. `Q∘inv` or `Q`. Since `inv` is an analytic involution of `GL(E)`,
  `Q = (Q∘inv)∘inv`, so neither is analytic (the proof below already fails on multiplication operators by units near `1`).
  Hence an instance `ContMDiffVectorBundle ω` for alternating-map bundles cannot exist in this generality.

## 1. Analytic ⟹ bounded bilinear lift (any characteristic)

Let `X = L(E,E)`, `Z` the target. Suppose `Q` has a power series `Σ p_n` at `0` on a ball of radius `r > 0`. For any
`y ≠ 0`, `q_n := ContinuousMultilinearMap.mkPiRing k (Fin n) (p_n(y,…,y))` has `‖q_n‖ ≤ ‖p_n‖‖y‖^n`, so `q` has radius
`≥ r/‖y‖ > 0` and `Σ q_n t^n = Q(ty) = t² Q(y)` for `|t| < r/‖y‖`. Uniqueness of one-variable power-series coefficients
over a nontrivially normed field (Mathlib `HasFPowerSeriesAt.eq_formalMultilinearSeries`; its proof is asymptotic, no
factorials, characteristic-free) gives `p_2(y,y) = Q(y)` for every `y`. So `P := p_2` is a bounded bilinear map (not
necessarily symmetric — only bilinearity is used below) with

    P(f,f) = Q(f)   for all f ∈ X.

Analyticity at `f₀` is equivalent to analyticity at `0`: `Q(f₀+h) = Q(f₀) + B(f₀,h) + Q(h)` with the bounded bilinear
`B(g,h)(m)(x,y) := m(gx,hy) + m(hx,gy)` (alternating in `(x,y)` in every characteristic, `‖B(g,h)‖ ≤ ‖g‖‖h‖`;
note `B ≠ 0` in characteristic 2).

## 2. The finite identity

`R` a commutative ring with `2 = 0`; `n = 2m+3`; `V = R^n` with standard basis; `𝒜 = R^n` with coordinatewise product,
acting on `V` by `m_a`. Identify `Λ²V` with alternating matrices (symmetric, zero diagonal) by `x∧y ↔ W(x,y)`; then
`Λ²(m_a)(ω) = (a⊗a)∘ω` (Schur product). `p_{ij}(a,b) := a_i b_j + a_j b_i`.

*Lifts.* A lift is a bilinear `ℛ : 𝒜×𝒜 → End_R(Λ²V)` with `ℛ(a,a) = Λ²(m_a)`. The sorted lift is
`ℛ_s(a,b)(ω)_{pq} := a_p b_q ω_{pq}` (`p<q`). If `D` is bilinear with `D(a,a) = 0` then `D(e_i,e_i) = 0` and
`D(e_i,e_j) = D(e_j,e_i)`, so (the source being free on the standard basis) `D = Σ_{i<j} p_{ij} D_{ij}`. Hence every lift is
`ℛ = ℛ_s + Σ_{i<j} p_{ij}(a,b) Ψ_{ij}` with `Ψ_{ij} ∈ End(Λ²V)` arbitrary, and for `e = {p<q}`

    φ_e(a,b) := [ℛ(a,b)(a∧b)]_e = a_p b_q p_{pq} + Σ_{i<j, c<d} Ψ_{ij}[e,cd] · p_{ij} p_{cd}.

*Contamination.* Let `G_e = φ_e + c_e` where `c_e ∈ R[a,b]` has **componentwise** bidegree `≤ (2,2)` and `≠ (2,2)`
(`deg_a ≤ 2` and `deg_b ≤ 2`, not both equal to 2). (Under the total-degree reading the lemma is false: bidegrees `(3,1)`
and `(1,3)` on two edges give coefficient `1 + c₁c₂` — `scripts/degtest.py`.)

*The invariant.* For an alternating matrix `G` define the divided power `G^{[m]} := Σ_{|J|=2m} Pf(G_J) e_J`
(`Pf(G_J) = Σ_{perfect matchings M of J} ∏_{e∈M} G_e`, no signs in characteristic 2, no division by `m!`; note the naive
`G∧G` is `0` in characteristic 2). Put

    𝔓(a,b) := G^{[m]} ∧ a² ∧ ab ∧ b² = Σ_{|J|=2m} Pf(G_J) · det₃[(a², ab, b²)_{[n]∖J}] ∈ R[a,b],

where `det₃ = ` permanent in characteristic 2, i.e. `Σ` over ordered triples `(i,j,r)` with `{i,j,r} = [n]∖J` of `a_i² a_j b_j b_r²`.

> **Lemma A.** The coefficient of `μ := a_1² b_2² ∏_{i≥3} a_i b_i` in `𝔓` is `1`, for every `Ψ` and every contamination.
> (It is the constant polynomial `1` in all these parameters.)

*Proof.* `𝔓 = Σ_{(i,j,r), M} (∏_{e∈M} G_e) · a_i² a_j b_j b_r²`, `M` a perfect matching of `[n]∖{i,j,r}`.
(1) `μ` has bidegree `(n,n)`, the componentwise maximum of every summand, so only the `(2,2)`-parts `φ_e` contribute.
(2) `deg_{a_i} μ = 2` only for `i = 1` and the border already contributes `a_i²`; likewise `deg_{b_r} μ = 2` only for `r = 2`.
So `i = 1`, `r = 2`, and `∏_{e∈M} φ_e` must contribute exactly the squarefree monomial `∏_{i∈J} a_i b_i`,
`J = [n]∖{1,2,j}`; no factor may involve the indices `1, 2`.
(3) Expand each `φ_e` into *orientation tuples*: the sorted part gives `a_p² b_q²` and `a_p a_q b_p b_q`; a parameter term
`Ψ_{ij}[e,cd] p_{ij} p_{cd}` gives the four tuples `a_x b_y a_z b_w` with `{x,y} = {i,j}`, `{z,w} = {c,d}`. Group the
summands by `(j, M, M', α)` where `M' ⊆ M` is the set of positions using a parameter term and `α` assigns to each
`e ∈ M'` an *ordered* pair of pairs `((ij),(cd))`, i.e. a specific parameter `Ψ_{ij}[e,cd]`. Within a group, the coefficient of
the target is the number (mod 2) of valid orientation choices. Positions in `M∖M'` must use the squarefree branch
`a_p a_q b_p b_q` (the branch `a_p²b_q²` has `deg_{a_p} = 2`), so they contribute `a`-indices and `b`-indices equal to
their own supports; therefore a choice of orientations on `M'` is valid iff every factor is squarefree and the multiset
of `a`-indices and the multiset of `b`-indices both equal `⋃M'` (each element once).
(4) The simultaneous flip `a_x b_y a_z b_w ↦ a_y b_x a_w b_z` at all `e ∈ M'` exchanges the two multisets, preserves
squarefreeness factor by factor (`a_x b_y a_z b_w` is squarefree iff `x≠z` and `y≠w`, which is the condition for the
flipped tuple), and has no fixed point (`x ≠ y`). It is an involution on the set of valid orientation tuples of the
group, so that set is even whenever `M' ≠ ∅`: every such group contributes `0`. (Checked on all 2 930 445 groups for
`n = 7`: `scripts/flipcheck.py`.)
(5) For `M' = ∅` each `(j,M)` contributes `1`; there are `(n−2)(2m−1)!! = (2m+1)!!` of them, an odd number. ∎

> **Corollary A′.** Let `R = k` be a non-archimedean valued field with **infinite residue field**, and suppose
> `G(a,b)` is an alternating matrix for all `a,b`. Then there are `a, b ∈ O_k^n` and `J` with `|J| = 2m` such that the
> principal minor satisfies `|det G(a,b)_J| = |Pf(G_J)|² ≥ 1`.

*Proof.* Let `γ := max_α |c_α| ≥ |c_μ| = 1` be the Gauss norm of `𝔓`; it is attained, so `γ ∈ |k^×|`. Choose `c` with
`|c| = γ^{-1}` (normalise by the **largest** coefficient, never by `c_μ`; large coefficients only raise `γ`). Then
`c𝔓 ∈ O_k[a,b]` has nonzero reduction over the residue field `κ`; `κ` infinite gives a `κ`-point where it is nonzero; lift
to `(a,b) ∈ O_k^{2n}`: `|𝔓(a,b)| = γ ≥ 1`. Since `|det₃| ≤ 1` on the unit polydisc, some `|Pf(G_J)| ≥ 1`, and
`det = Pf²` for alternating matrices over any commutative ring. ∎

Why *infinite*: `deg_{a_p} 𝔓 ≤ n−1`, so `|κ| ≥ n` would do for one block, but §4 needs `n → ∞`. Over `F_2` the
conclusion of A′ is genuinely false with contamination (`scripts/witness_f2.py` exhibits a lift + contamination with
`𝔓 ≡ 0` on all `F_2`-points, n = 5); over `F_4, F_8, F_16` and `n = 5` it holds for **every** lift and contamination
(exhaustive linear algebra over the full 2710-parameter space, `scripts/exact.py`).

## 2′. A simpler form of the finite identity (found while formalizing; this is what the Lean proof uses)

No border and no orientation bookkeeping are needed. Take a block of **even** size `n = 2m`, write `X_i, Y_i` for the
coordinates of `a, b`, let `τ` swap `X ↔ Y` and let `δ` be the substitution `Y := X`. For an edge `e = {p,q}` let
`g_e(X,Y) := [Φ(x,y;x,y)]_e` be the top (bidegree `(2,2)`) part of the block entry. From `Φ(a,a;x,y) = W(ax,ay)`,
alternation in `(x,y)` and `2 = 0`:

    τ g_e = g_e + X_p²Y_q² + X_q²Y_p²,        δ g_e = 0.

Put `g'_e := g_e + X_p²Y_q²`; then `τ g'_e = g'_e` and `δ g'_e = X_p²X_q²`.

* **Balanced-coefficient lemma.** If `τ f = f` (char 2) then for every `S` the coefficient of `∏_{i∈S} X_iY_i` in `f` equals the
  coefficient of `∏_{i∈S} X_i²` in `δ f`: the fibre of `δ` over that monomial is permuted by `τ`, coefficients are
  `τ`-invariant, pairs cancel, and the only fixed point is the balanced monomial.
* Products containing a factor `X_p²Y_q²` have no squarefree monomials, so for a perfect matching `M` of the block
  `coeff_ν ∏_{e∈M} g_e = coeff_ν ∏ g'_e = coeff_{∏X_i²} ∏_{e∈M} X_p²X_q² = 1`, where `ν = ∏_i X_iY_i`.
* Lower-order contamination has total degree `≤ 3 < 4`, so it cannot reach `ν` (total degree `4m`).
* In characteristic 2 a symmetric zero-diagonal matrix has `det = Σ_{matchings} (∏_{e} G_e)²`, and squaring is additive on
  coefficients, so `coeff_{ν²} det G = #{perfect matchings} = (2m−1)!! = 1`.

Hence `det G(a,b)`, a polynomial in the block variables, has a coefficient equal to `1`, and Corollary A′ gives unit
vectors with `|det G_t| ≥ 1` for the **whole** `2m × 2m` block. (Numerically checked: `scripts/nobord.py`.) §4 is unchanged
except that blocks have even size and `J_t = I_t`.

## 3. Multilinear Phillips lemma (the only use of "not spherically complete")

**Fact (van der Put 1969, Thm 3.2).** `k` is spherically complete ⟺ `(ℓ^∞/c₀)' ≠ 0`.

**(i) `(ℓ^∞)' = c₀`.** Let `φ ∈ (ℓ^∞)'`, `b_i := φ(e_i)`. If `b ∉ c₀`, pick `i_1<i_2<…` with `|b_{i_n}| ≥ ε` and the
bounded operator `J y := Σ_n y_n b_{i_n}^{-1} e_{i_n}` (coordinatewise). `ψ := φ∘J` has `ψ(e_n) = 1`, so `ψ(y) = Σ y_n` on
`c₀`. With `S` the right shift, `χ := ψ∘(I−S)` vanishes on `c₀` (telescoping), hence `χ = 0` by the Fact; but
`(I−S)𝟙 = e_1`, so `χ(𝟙) = ψ(e_1) = 1`. Contradiction. So `b ∈ c₀`, and `φ − Σ b_i(·)_i` kills `c₀`, hence is `0`:
`φ(x) = Σ b_i x_i` for **all** `x ∈ ℓ^∞`, and `(ℓ^∞)' ≅ c₀` isometrically.

**(ii) Operators.** Every bounded `T : ℓ^∞ → c₀(J)` (`J` countable) has a jointly decaying matrix `a_{ij} = (Te_i)_j`:
for each `ε` only finitely many `|a_{ij}| > ε`. *Proof.* Rows are in `c₀(J)`; columns are in `c₀` by (i). If infinitely
many entries exceed `ε`, finiteness of rows and columns gives an infinite partial permutation `(i_t,j_t)`; choose
`t_1<t_2<…` recursively so that `|a_{i_{t_s} j_{t_r}}| ≤ ε` and `|a_{i_{t_r} j_{t_s}}| ≤ ε` for `s<r` (each condition
excludes finitely many candidates). For `x = 𝟙_{\{i_{t_r}\}}`, `(Tx)_j = Σ_i a_{ij} x_i` by (i), and by the ultrametric
inequality the diagonal term dominates: `|(Tx)_{j_{t_r}}| = |a_{i_{t_r} j_{t_r}}| > ε` for all `r`, contradicting
`Tx ∈ c₀(J)`. ∎

**(iii) Induction.** `Mult^d(ℓ^∞;k) ≅ c₀(ℕ^d)` isometrically, via `h(i) = λ(e_{i_1},…,e_{i_d})` and
`λ(u) = Σ h(i) ∏ u_{j,i_j}` (unconditionally convergent): apply (ii) to `u_d ↦ λ(·,…,·,u_d) ∈ Mult^{d-1} ≅ c₀(ℕ^{d-1})`.

**(iv) Tails.** If `‖u_j‖ ≤ 1` and some `u_j` is supported in `[N,∞)`, then `|λ(u)| ≤ sup{|h(i)| : i_j ≥ N}`; as
`{|h| > ε}` is finite, `T_N(λ) := sup |λ(u)|` over all such unit tuples tends to `0`. (Joint decay is what gives the
uniformity; slot-wise decay would not.) This is false on `c₀`: `λ(u,v) = Σ u_i v_i` has `T_N = 1`.

## 4. Gluing

Assume a bounded bilinear `P` with `P(f,f) = Q(f)`. `‖m_a‖ = ‖a‖_∞`; `m₀ := W` is a bounded alternating map `E×E → F`
(`W(x,x) = 2x⊗x = 0`; Mathlib's alternating condition is `map_eq_zero_of_eq`), `‖W‖ ≤ 1`. Define

    Φ(a,b;x,y) := P(m_a, m_b)(m₀)(x,y) ∈ F,       a,b,x,y ∈ ℓ^∞.

`Φ` is 4-linear, `‖Φ‖ ≤ C := max(1,‖P‖)`, `Φ(a,b;x,x) = 0`, and `Φ(a,a;x,y) = W(ax,ay)`.
Every element of `F` is symmetric with zero diagonal (closed conditions, true for each `W(x,y)`) and is a sup-norm limit
of finite-rank matrices (`rank W(x,y) ≤ 2`). Each entry `λ_{pq}(a,b,x,y) := Φ(a,b;x,y)_{pq}` is a fixed bounded 4-linear
form on `ℓ^∞`, so §3(iv) applies to it.

*Block lifts.* For a finite `I ⊂ ℕ` and `a,b,x,y` supported in `I`, `Φ(a,b;·,·)|_{I×I}` is bilinear and vanishes on the
diagonal, hence factors through `Λ²(k^I)`; its values are alternating `I×I` matrices, identified with `Λ²(k^I)` by the same
`W`-correspondence; and `Φ(a,a;x,y)|_I = (a⊗a)∘W(x,y)|_I`. So `ℛ_I(a,b)(x∧y) := Φ(a,b;x,y)|_{I×I}` is a lift in the sense of §2.

*Construction.* All `ε`'s and `η` below are **real** constants (not field elements). Inductively for `t = 1,2,…`:
1. choose a block `I_t ⊂ [N_t, ∞)` (with `N_1 = 0`), `|I_t| = 2m_t+3`, `m_t ≥ t`, to the right of `I_{t-1}`
   (in the §2′ form used by Lean: `|I_t| = 2m_t` even, and below `J_t = I_t`);
2. with `a' := Σ_{s<t} a_s`, `b' := Σ_{s<t} b_s` (fixed), the matrix
   `G_t(a_t,b_t) := Φ(a'+a_t, b'+b_t; a'+a_t, b'+b_t)|_{I_t×I_t}` is, in `k[a_{t,i}, b_{t,i} : i ∈ I_t]`, of degree `≤ 2` in
   `a_t` and `≤ 2` in `b_t` (slots 1,3 carry `a`, slots 2,4 carry `b`), with `(2,2)`-part exactly
   `ℛ_{I_t}(a_t,b_t)(a_t∧b_t)`; and `(a'+a_t)²|_{I_t} = a_t²`, `(a'+a_t)(b'+b_t)|_{I_t} = a_t b_t`, `(b'+b_t)²|_{I_t} = b_t²`
   (disjoint supports). This is exactly the hypothesis of Lemma A, so by Corollary A′ choose `a_t, b_t ∈ O_k^{I_t}` and
   `J_t ⊆ I_t`, `|J_t| = 2m_t`, with `|det G_t[J_t]| ≥ 1`;
3. put `ε_t := ½ C^{-2m_t}` and choose `N_{t+1}` with `T_{N_{t+1}}(λ_{pq}) < ε_t` for the finitely many `(p,q) ∈ I_t²`.

Let `a, b ∈ ℓ^∞` be defined coordinatewise by `a|_{I_t} = a_t`, `b|_{I_t} = b_t`, zero elsewhere (`‖a‖,‖b‖ ≤ 1`). This is
**not** a norm-convergent series (`‖a − a^{≤t}‖ = 1`); every use below is the finite splitting `a = a^{≤t} + a^{>t}`.
Let `𝒪 := Φ(a,b;a,b) ∈ F`. Expanding in the four slots gives 16 terms; one is `Φ(a^{≤t},b^{≤t};a^{≤t},b^{≤t})`, whose
`I_t`-block is `G_t(a_t,b_t)`, and the other 15 contain an argument supported in `[N_{t+1},∞)`, so their `I_t`-blocks have
entries `< ε_t`. Hence `‖𝒪|_{I_t} − G_t‖ < ε_t`. Expanding `det(G+E) = Σ_S det(`columns of `E` on `S`, of `G` off `S)`, the
terms with `S ≠ ∅` are bounded by `ε_t C^{2m_t−1} = ½C^{-1} < 1 ≤ |det G_t[J_t]|`, so by the ultrametric inequality

    |det 𝒪[J_t]| = |det G_t[J_t]| ≥ 1     for every t.

*Contradiction.* Now fix `η := (2C)^{-1}`. Since `𝒪 ∈ F`, there is a finite-rank `R = Σ_{i≤r} u_i⊗v_i` with
`‖𝒪 − R‖ < η`; then `‖R‖ ≤ max(‖𝒪‖, η) ≤ C` and `rank R[J] ≤ r`. Expanding `det(R[J] + E[J])` multilinearly in columns,
terms using more than `r` columns of `R[J]` vanish and the others are bounded by `C^s η^{N−s} ≤ C^r η^{N−r}` (`s ≤ r`,
`η ≤ C`, `N = 2m_t`). Choosing `t` with `m_t > r`: `|det 𝒪[J_t]| ≤ C^r (2C)^{-(2m_t−r)} < 1`. Contradiction. ∎

## 5. Why it does not prove too much (each known positive result kills a specific step)

| regime (where `Q` IS analytic) | step that fails |
|---|---|
| `char k ≠ 2` | Lemma A: alternating differences are carried by `a_ib_j − a_jb_i`, the flip pairs monomials with sign `+`, no cancellation; for the polarisation lift `φ_e = ½(a_p²b_q² − a_q²b_p²)` has no squarefree part and the `μ`-coefficient is `0`. Residue characteristic 2 is not enough (`‖½‖ > 1` breaks the reduction). |
| `dim E < ∞` | §4 needs `m_t → ∞`. |
| `E = c₀` (any based `E`) | §3(iv) is false on `c₀`, and the glued `a, b` are not in `c₀`; the sorted lift converges there. (`ℓ^∞` has no t-orthogonal base here: `c₀(J)' = ℓ^∞(J)` is not of countable type, `(ℓ^∞)' = c₀` is.) |
| `k` discretely valued (e.g. `F_2((t))`) | complete + discrete ⟹ spherically complete ⟹ Hahn–Banach ⟹ a functional with `T_N = 1`; also the residue field is finite. |
| `F` spherically complete | our `F` is not: `ω ↦ ω_{12} W(e_1,e_2)` is a norm-≤1 projection onto a line isometric to `k`. |
| `E = ℓ^∞`, `F ∈ {k, c₀(J), ℓ^∞(J)}` | §4 needs (i) `W ∈ Alt²(E,F)`, which fails for `k`, `c₀(J)`; (ii) finite-rank approximability of every element of `F`, which fails for `ℓ^∞(ℕ×ℕ)`. The sorted lift for the big target leaves `F`: `f = id`, `g = m_z`, `z = (0,1,0,1,…)`, `m = W`, `x = 𝟙`, `y = z` gives the staircase `[p odd, q even, p<q]`, whose `(2a−1,2b)` blocks are unit upper triangular. |

## 6. What else came out (finite model, characteristic 2)

* **Quadratic refinements of the wedge** (`κ : V → Λ²V`, `κ(a+b) = κ(a)+κ(b)+a∧b`, `κ(ca) = c²κ(a)`), `n` odd: the polynomial
  `κ(a)^{[(n−1)/2]} ∧ a` has the monomial `a_1⋯a_n` with coefficient `n!!`, odd, independent of the free part `Σ a_i² κ_i`.
  So every projection of `V⊗V` onto the alternating tensors sends some `a⊗a` to rank `≥ n−1`.
* **Half-selectors** (`h : Alt_n → M_n` linear, `h + hᵗ = id`): over `F_2` and `F_4`, for `n ≤ 5`, the number of planes `P` on
  which `h(ω_P)|_{P^⊥}` is nondegenerate is always odd (numerical; `scripts/gfq.py`, `rel_find.py`) — the Hasse–Witt shadow
  of an anticanonical section on `Gr(2,n)`; exact solver: no half-selector on `F_2^4` has all decomposable ranks `≤ 2`.
* These say that neither the symmetric nor the alternating matrices are complemented in `ℓ^∞ ⊗̂ ℓ^∞` here; §4 is the
  statement that the analytic lift *itself* fails, which is strictly more.

## 7. Open

* Characteristic `p ≥ 3` (degree-`p` forms): the mechanism should persist, but odd-degree forms have no Pfaffian-type
  top power (`ω∧ω = 0`), so a different invariant of the right (anticanonical) degree is needed.
* Spherically complete densely valued `k` (e.g. Hahn series `F_2((t^ℚ))`): §3 fails; unknown.
* Finite residue field with dense valuation: only Corollary A′ needs repair (a contamination-free gluing, or points in
  an unramified extension).

Scripts: `scripts/` (`full5.py`, `full7.py`, `sym_lemmaA.py` formal identity;
`flipcheck.py` involution; `degtest.py` sharpness of the bidegree hypothesis; `exact.py`, `witness_f2.py` Corollary A′ over
small fields; `sec4_faithful.py` finite model of §4; `p6_escape.py` the big-target lift leaving `F`; `liftdiagonal.py`,
`topcoef*.py` the original discovery runs).

## 8. Lean formalization (2026-09-19)

This repository (`AltCounter/`), about 3600 lines, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

    theorem not_analyticAt_Q_of_NSC [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
        (hres : InfiniteResidue 𝕜) (hnsc : NSC 𝕜) : ¬ AnalyticAt 𝕜 (Q 𝕜) 0

`Q 𝕜 f = ContinuousAlternatingMap.compContinuousLinearMapCLM f` on `(ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F 𝕜`; `NSC` is
"(ℓ^∞/c₀)' = 0" (a functional on `ℓ^∞` killing every standard basis vector is zero); `InfiniteResidue` is "arbitrarily
many unit-ball points pairwise at distance 1".

Formalized: the bilinear lift of §1, the identity of §2′ (with Corollary A′), §3 and §4 — giving non-analyticity **at `0`**.
Not formalized: the existence of a field with these properties (van der Put's theorem and the completed algebraic closure
of `𝔽₂((t))`), the §1 reduction to an arbitrary base point, the border form of Lemma A in §2 (superseded by §2′), and the
consequences listed in §0 (index types with more than two elements, the bundle-level statement).
