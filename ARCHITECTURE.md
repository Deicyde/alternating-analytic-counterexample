# Development notes

## Dependency graph
Defs → {Pfaffian, GaussPoint, DetBounds}; Pfaffian → Balanced; {Balanced, GaussPoint} → FiniteLemma;
{FiniteLemma, DetBounds} → Gluing; Criterion (independent); {Gluing, Criterion} → Main;
FiniteLemma → PhillipsOne → Phillips; {Main, Phillips} → MainNSC → Check.

## Local single-file builds (optional)
`lake build` is the supported way to build. On a machine that already has a *built* Mathlib checkout at the pinned
commit, single files can be compiled without creating `.lake/` here:

    (cd /path/to/mathlib4 && lake env printenv LEAN_PATH) > .leanpath
    ./build.sh AltCounter/Foo.lean        # writes .build/AltCounter/Foo.olean, at most 3 compiles at a time

## Mathlib API notes (this Mathlib version)
* Multivariate polynomial coefficients are `p.coeff m` (polynomial first).
* Continuous alternating maps into a `Submodule` subtype break instance search for the operator-norm structure on
  `(E [⋀^ι]→L[𝕜] ↥S) →L[𝕜] …`; `F` is therefore a type synonym of the submodule with `inferInstanceAs` instances.
* `⊤ : WithTop ℕ∞` is the analytic smoothness exponent `ω`.
