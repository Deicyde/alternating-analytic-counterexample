/-
The counterexample: over an ultrametric field `𝕜` of characteristic 2 with infinite residue field and the
multilinear Phillips property (e.g. the completion of an algebraic closure of `𝔽₂((t))`), with `E = ℓ^∞(ℕ, 𝕜)` and
`F` the closed span of the matrices `x ⊗ y + y ⊗ x` in `ℓ^∞(ℕ × ℕ, 𝕜)`, the precomposition map
`f ↦ (m ↦ m ∘ (f, f))` on continuous alternating 2-forms is not analytic.
-/
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import AltCounter.Gluing
import AltCounter.Criterion

namespace AltCounter

open BoundedContinuousFunction

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- The matrix `x ⊗ y + y ⊗ x`, as a bounded function on `ℕ × ℕ`. -/
noncomputable def Wfun (x y : Linf 𝕜) : (ℕ × ℕ) →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun pq => x pq.1 * y pq.2 + y pq.1 * x pq.2) (2 * (‖x‖ * ‖y‖)) (by
      intro pq
      calc ‖x pq.1 * y pq.2 + y pq.1 * x pq.2‖
          ≤ ‖x pq.1 * y pq.2‖ + ‖y pq.1 * x pq.2‖ := norm_add_le _ _
        _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by
            gcongr
            · rw [norm_mul]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
            · rw [norm_mul, mul_comm]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
        _ = 2 * (‖x‖ * ‖y‖) := by ring)

/-- The closed linear span of the matrices `x ⊗ y + y ⊗ x`, as a submodule of `ℓ^∞(ℕ × ℕ)`. -/
noncomputable def FSub : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜) :=
  (Submodule.span 𝕜 (Set.range fun xy : Linf 𝕜 × Linf 𝕜 => Wfun 𝕜 xy.1 xy.2)).topologicalClosure

/-- The target space `F`: the closed linear span of the matrices `x ⊗ y + y ⊗ x`, as a normed space.
(A type synonym of the submodule, so that instance search treats it as an ordinary normed space.) -/
def F : Type _ := ↥(FSub 𝕜)

noncomputable instance : NormedAddCommGroup (F 𝕜) := inferInstanceAs (NormedAddCommGroup ↥(FSub 𝕜))
noncomputable instance : NormedSpace 𝕜 (F 𝕜) := inferInstanceAs (NormedSpace 𝕜 ↥(FSub 𝕜))

/-- The inclusion of `F` into `ℓ^∞(ℕ × ℕ)`. -/
noncomputable def F.incl : F 𝕜 →L[𝕜] ((ℕ × ℕ) →ᵇ 𝕜) := (FSub 𝕜).subtypeL

/-- The precomposition map on continuous alternating 2-forms `ℓ^∞ × ℓ^∞ → F`. -/
noncomputable def Q (f : Linf 𝕜 →L[𝕜] Linf 𝕜) :
    (Linf 𝕜) [⋀^Fin 2]→L[𝕜] (F 𝕜) →L[𝕜] (Linf 𝕜) [⋀^Fin 2]→L[𝕜] (F 𝕜) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM f

variable {𝕜}

/-- **Main theorem.** `Q` is not analytic at `0`. -/
theorem not_analyticAt_Q [IsUltrametricDist 𝕜] [CharP 𝕜 2] (hres : InfiniteResidue 𝕜)
    (htail : TailProperty 𝕜) : ¬ AnalyticAt 𝕜 (Q 𝕜) 0 := by
  sorry

/-- In particular `Q` is not `C^ω`: the restriction to `n : ℕ∞` in the smooth statement is sharp. -/
theorem not_contDiff_omega_Q [IsUltrametricDist 𝕜] [CharP 𝕜 2] (hres : InfiniteResidue 𝕜)
    (htail : TailProperty 𝕜) : ¬ ContDiff 𝕜 ⊤ (Q 𝕜) := by
  sorry

end AltCounter
