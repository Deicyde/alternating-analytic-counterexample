/-
Comparator challenge (Mathlib only; every constant in the statements is a Mathlib constant).

Precomposition on continuous alternating maps is NOT analytic in characteristic 2.

Let `𝕜` be a complete ultrametric field of characteristic 2 such that
* the residue field is infinite (`hres`: arbitrarily many points of the unit ball pairwise at distance `1`), and
* `(ℓ^∞ / c₀)' = 0` (`hdual`: a continuous linear functional on `ℓ^∞ = ℕ →ᵇ 𝕜` that vanishes on every null sequence
  is zero) — by van der Put (1969) this holds for every complete non-archimedean field that is not spherically
  complete, e.g. the completion of an algebraic closure of `𝔽₂((t))`.
Then there is a normed space `F` over `𝕜` such that the map
`f ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM f` (`m ↦ m ∘ (f, f)`) on continuous alternating 2-forms
`ℓ^∞ × ℓ^∞ → F` is not analytic at `0`, hence not `C^ω`.
-/
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Ultra

open BoundedContinuousFunction Filter Topology

universe u

namespace AlternatingAnalyticChallenge

theorem exists_not_analyticAt_compContinuousLinearMapCLM
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
    (hres : ∀ N : ℕ, ∃ t : Fin N → 𝕜, (∀ i, ‖t i‖ ≤ 1) ∧ ∀ i j, i ≠ j → ‖t i - t j‖ = 1)
    (hdual : ∀ φ : (ℕ →ᵇ 𝕜) →L[𝕜] 𝕜,
      (∀ x : ℕ →ᵇ 𝕜, Tendsto (fun i => x i) atTop (𝓝 0) → φ x = 0) → φ = 0) :
    ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
      ¬ AnalyticAt 𝕜
        (fun f : (ℕ →ᵇ 𝕜) →L[𝕜] (ℕ →ᵇ 𝕜) =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F) →L[𝕜] ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F))) 0 := by
  sorry

theorem exists_not_contDiff_omega_compContinuousLinearMapCLM
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
    (hres : ∀ N : ℕ, ∃ t : Fin N → 𝕜, (∀ i, ‖t i‖ ≤ 1) ∧ ∀ i j, i ≠ j → ‖t i - t j‖ = 1)
    (hdual : ∀ φ : (ℕ →ᵇ 𝕜) →L[𝕜] 𝕜,
      (∀ x : ℕ →ᵇ 𝕜, Tendsto (fun i => x i) atTop (𝓝 0) → φ x = 0) → φ = 0) :
    ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
      ¬ ContDiff 𝕜 (⊤ : WithTop ℕ∞)
        (fun f : (ℕ →ᵇ 𝕜) →L[𝕜] (ℕ →ᵇ 𝕜) =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F) →L[𝕜] ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F))) := by
  sorry

end AlternatingAnalyticChallenge
