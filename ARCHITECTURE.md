# Lean formalization of the characteristic-2 counterexample

Goal (`AltCounter/Main.lean`): over an ultrametric field `𝕜` of characteristic 2 with infinite residue field
(`InfiniteResidue`) and the multilinear Phillips property (`TailProperty`), with `E = ℓ^∞(ℕ,𝕜)` and `F` = closed span of
`x⊗y + y⊗x` in `ℓ^∞(ℕ×ℕ,𝕜)`, the map `Q f = compContinuousLinearMapCLM f` on alternating 2-forms is not analytic at `0`.

## Build
No lake project. Mathlib is prebuilt at `~/Desktop/LEAN/mathlib4-altpr` (Lean v4.34.0-rc2, recent Mathlib with the
`module` system). Compile ONE file with `./build.sh AltCounter/Foo.lean` from this directory (takes 30-90 s; it prints
errors/warnings; it writes `.build/AltCounter/Foo.olean`, which files importing `AltCounter.Foo` need). NEVER run
`lake build`, never touch the Mathlib checkout, never `import Mathlib` (memory: keep imports targeted; you may add
imports you need). To look up Mathlib API use grep/rg on `~/Desktop/LEAN/mathlib4-altpr/Mathlib/` and small scratch
files compiled with `LEAN_PATH="$(cat .leanpath):$PWD/.build" lean /tmp/yourname_scratch.lean`.
API gotcha: for multivariate polynomials the coefficient is now `p.coeff m` (polynomial first): `MvPolynomial.coeff_monomial`
states `((monomial n) a).coeff m = ...`.

## Rules
* Work ONLY in your assigned file. Do not change the statements (names, hypotheses, conclusions) of the theorems/defs
  already present: other files depend on them. You may add helper lemmas/defs above them and extra imports.
* No `sorry`, no `admit`, no new `axiom`, no `native_decide`, in the final file. `./build.sh` must succeed with no errors.
* If you become convinced a statement is false or unprovable as stated, STOP and report exactly why and the minimal fix.
* Keep proofs robust: prefer explicit terms/`simp only` over fragile big `simp` calls when convenient; long proofs are fine.

## Dependency graph (all statements are fixed, so every file can be worked on independently)
Defs → {Pfaffian, GaussPoint, DetBounds}; Pfaffian → Balanced; {Balanced, GaussPoint} → FiniteLemma;
{FiniteLemma, DetBounds} → Gluing; Criterion (independent); {Gluing, Criterion} → Main.
