# Precomposition on continuous alternating maps is not analytic in characteristic 2

A counterexample, with a complete Lean 4 / Mathlib formalization.

**Context.** For normed spaces `E, E', F` over a nontrivially normed field `𝕜`, the map
`f ↦ (m ↦ m ∘ (f, …, f))` from `E →L[𝕜] E'` to `(E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)`
(`ContinuousAlternatingMap.compContinuousLinearMapCLM`) is `C^n` for every `n : ℕ∞`, in every characteristic
(Mathlib PR [#43548](https://github.com/leanprover-community/mathlib4/pull/43548)), and analytic when `(card ι)!` is
invertible in `𝕜` (polarisation). This repository shows that the analytic (`n = ω`) statement is **false** in
characteristic 2 in infinite dimensions, so the restriction `n : ℕ∞` is sharp. This is what obstructs a
`ContMDiffVectorBundle ω` instance for bundles of continuous alternating maps in full generality.

## The theorem (`AltCounter/MainNSC.lean`)

```lean
theorem not_analyticAt_Q_of_NSC
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
    (hres : InfiniteResidue 𝕜) (hnsc : NSC 𝕜) : ¬ AnalyticAt 𝕜 (Q 𝕜) 0

theorem not_contDiff_omega_Q_of_NSC ... : ¬ ContDiff 𝕜 ⊤ (Q 𝕜)      -- `⊤ : WithTop ℕ∞` is `ω`
```

* `Linf 𝕜 := ℕ →ᵇ 𝕜` is `ℓ^∞(ℕ, 𝕜)`.
* `F 𝕜` is the closed linear span, in `ℓ^∞(ℕ × ℕ, 𝕜)`, of the matrices `x ⊗ y + y ⊗ x`.
* `Q 𝕜 f := ContinuousAlternatingMap.compContinuousLinearMapCLM f`, acting on `(Linf 𝕜) [⋀^Fin 2]→L[𝕜] F 𝕜`.
* `InfiniteResidue 𝕜`: for every `N` there are `N` points of the unit ball pairwise at distance exactly `1`
  (i.e. the residue field is infinite).
* `NSC 𝕜`: a continuous linear functional on `ℓ^∞` that vanishes on every unit vector is zero, i.e. `(ℓ^∞/c₀)' = 0`.

All theorems are free of `sorry` and depend only on `propext`, `Classical.choice`, `Quot.sound`
(`AltCounter/Check.lean` prints this).

### What is *not* formalized

The existence of a field satisfying the hypotheses. On paper: by van der Put (*Espaces de Banach non archimédiens*,
Bull. SMF 97 (1969), Thm 3.2) a complete non-archimedean field satisfies `(ℓ^∞/c₀)' = 0` iff it is **not spherically
complete**; the completion of an algebraic closure of `𝔽₂((t))` is complete, of characteristic 2, not spherically
complete, and has residue field `𝔽̄₂`. Mathlib has neither this field nor van der Put's theorem, so the Lean
theorem is stated for an arbitrary field with these properties as explicit hypotheses (they are hypotheses, not axioms).
Characteristic `p ≥ 3` (forms of degree `p`) is open.

## Idea of the proof

1. *(Criterion)* An analytic map which is homogeneous of degree 2 is the diagonal of a bounded bilinear map `P`
   (uniqueness of one-variable power-series coefficients; valid in every characteristic).
2. *(FiniteLemma, Balanced, Pfaffian, GaussPoint)* Restrict `P` to multiplication operators on `ℓ^∞` and evaluate on the
   universal alternating form `W(x,y) = x⊗y + y⊗x`. On any coordinate block of even size, the block matrix is a
   polynomial in the block variables, symmetric with zero diagonal. In characteristic 2 its determinant is a sum of
   squares over perfect matchings; a swap-invariance argument shows that every matching product has coefficient `1` at
   the monomial `∏ XᵢYᵢ`, and the number of perfect matchings is odd, so the determinant has a coefficient equal to `1`.
   With an infinite residue field this yields unit vectors at which the block has `‖det‖ ≥ 1`.
3. *(PhillipsOne, Phillips)* From `(ℓ^∞/c₀)' = 0`, bounded multilinear forms on `ℓ^∞` are uniformly small as soon as one
   argument is supported far out.
4. *(Gluing, DetBounds)* Hence finitely-supported bad blocks of growing size can be glued into a single pair
   `a, b ∈ ℓ^∞`; the resulting element of `F` has minors of norm `≥ 1` of every size, contradicting the fact that every
   element of `F` is a uniform limit of finite-rank matrices.

The full mathematical write-up is in [`paper/COUNTEREXAMPLE.md`](paper/COUNTEREXAMPLE.md); exploratory and verification
scripts (pure Python) are in [`scripts/`](scripts/).

## Building

```bash
lake exe cache get
lake build
```

Lean `v4.34.0-rc2`, Mathlib pinned in `lakefile.toml` / `lake-manifest.json`. CI builds the project on every push.
(`build.sh` is a local convenience script that compiles a single file against an already-built Mathlib checkout whose
`LEAN_PATH` is stored in an untracked `.leanpath` file; see `ARCHITECTURE.md`.)

| file | lines | content |
|---|---|---|
| `Defs` | 45 | `Linf`, `InfiniteResidue`, `IsBdd4`, `TailProperty` |
| `Pfaffian` | 230 | char-2 determinant as a sum of squares over perfect matchings; their number is odd |
| `Balanced` | 460 | the key coefficient identity |
| `GaussPoint` | 175 | a polynomial with a coefficient of norm `≥ 1` has a value of norm `≥ 1` on the unit polydisc |
| `DetBounds` | 209 | ultrametric determinant bounds (perturbation, closeness to low rank) |
| `FiniteLemma` | 473 | every even block has unit vectors with `‖det‖ ≥ 1` |
| `Gluing` | 402 | the core contradiction |
| `Criterion` | 65 | analytic + homogeneous of degree 2 ⟹ bilinear lift |
| `Main` | 476 | assembly; `not_analyticAt_Q` under `TailProperty` |
| `PhillipsOne`, `Phillips` | ~1000 | `NSC ⟹ TailProperty` |
| `MainNSC`, `Check` | | final statements, axiom check |

## Provenance

The counterexample, its proof, and this formalization were produced by an AI system (Anthropic's Claude, working in
Claude Code with Jack McCarthy), in September 2026. The informal proof was attacked by independent AI referee agents and
the argument is fully machine-checked by Lean as stated above; the informal write-up and the unformalized field-existence
step have **not** yet been reviewed by a human expert in non-archimedean functional analysis.
