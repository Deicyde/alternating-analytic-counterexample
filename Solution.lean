/-
Comparator solution: proves the two theorems of `Challenge.lean` verbatim, from the project's formalization.
-/
import AltCounter.Bridge

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
            ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F) →L[𝕜] ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F))) 0 :=
  ⟨AltCounter.F 𝕜, inferInstance, inferInstance,
    AltCounter.not_analyticAt_Q_of_NSC hres (AltCounter.nsc_of_dual hdual)⟩

theorem exists_not_contDiff_omega_compContinuousLinearMapCLM
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
    (hres : ∀ N : ℕ, ∃ t : Fin N → 𝕜, (∀ i, ‖t i‖ ≤ 1) ∧ ∀ i j, i ≠ j → ‖t i - t j‖ = 1)
    (hdual : ∀ φ : (ℕ →ᵇ 𝕜) →L[𝕜] 𝕜,
      (∀ x : ℕ →ᵇ 𝕜, Tendsto (fun i => x i) atTop (𝓝 0) → φ x = 0) → φ = 0) :
    ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
      ¬ ContDiff 𝕜 (⊤ : WithTop ℕ∞)
        (fun f : (ℕ →ᵇ 𝕜) →L[𝕜] (ℕ →ᵇ 𝕜) =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F) →L[𝕜] ((ℕ →ᵇ 𝕜) [⋀^Fin 2]→L[𝕜] F))) :=
  ⟨AltCounter.F 𝕜, inferInstance, inferInstance,
    AltCounter.not_contDiff_omega_Q_of_NSC hres (AltCounter.nsc_of_dual hdual)⟩

end AlternatingAnalyticChallenge
