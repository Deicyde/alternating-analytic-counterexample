# Analyticity of precomposition on alternating maps fails in characteristic 2 — Lean formalization

`AltCounter/Main.lean`:

```lean
theorem not_analyticAt_Q [IsUltrametricDist 𝕜] [CharP 𝕜 2] (hres : InfiniteResidue 𝕜)
    (htail : TailProperty 𝕜) : ¬ AnalyticAt 𝕜 (Q 𝕜) 0
theorem not_contDiff_omega_Q ... : ¬ ContDiff 𝕜 ⊤ (Q 𝕜)
```

where `𝕜` is a nontrivially normed field, `Linf 𝕜 = ℕ →ᵇ 𝕜` is `ℓ^∞`, `F 𝕜` is the closed span of the matrices
`x ⊗ y + y ⊗ x` in `ℓ^∞(ℕ × ℕ)`, and
`Q 𝕜 f = ContinuousAlternatingMap.compContinuousLinearMapCLM f` on `(Linf 𝕜) [⋀^Fin 2]→L[𝕜] F 𝕜`.
Both theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (`AltCounter/Check.lean`).

Field hypotheses (explicit, not axioms):
* `InfiniteResidue 𝕜`: arbitrarily many points of the unit ball pairwise at distance exactly `1`
  (the residue field is infinite);
* `TailProperty 𝕜`: bounded 4-linear forms on `ℓ^∞` are uniformly small once one argument is supported far out.
  `AltCounter/Phillips.lean` derives it from `NSC 𝕜` : "a continuous functional on `ℓ^∞` killing all unit vectors is `0`",
  i.e. `(ℓ^∞/c₀)' = 0`, which by van der Put (1969, Thm 3.2) holds exactly for complete non-archimedean fields that are
  not spherically complete, e.g. the completion of an algebraic closure of `𝔽₂((t))`. The existence of such a field is
  NOT formalized (Mathlib does not have it).

Files: `Defs` (hypotheses), `Pfaffian` (char-2 determinant = sum of squares over perfect matchings; their number is odd),
`Balanced` (the key coefficient identity via swap-invariance), `GaussPoint` (a polynomial with a unit coefficient takes a
unit value on the unit polydisc), `DetBounds` (ultrametric determinant bounds), `FiniteLemma` (every block of even size
has unit vectors with `‖det‖ ≥ 1`), `Gluing` (the core contradiction), `Criterion` (analytic + homogeneous of degree 2 ⟹
bilinear lift), `Main`, `PhillipsOne`/`Phillips` (tail property from `NSC`), `MainNSC`.

Build: no lake project; `./build.sh AltCounter/Foo.lean` compiles one file against the prebuilt Mathlib checkout listed in
`.leanpath` (see `ARCHITECTURE.md`). Order: Defs, Pfaffian, GaussPoint, DetBounds, Balanced, Criterion, FiniteLemma,
Gluing, Main, PhillipsOne, Phillips, MainNSC, Check.

Mathematics: `~/Desktop/notes/alt-bundle-analytic-COUNTEREXAMPLE.md`.
