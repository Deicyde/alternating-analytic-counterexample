/-
Tails of bounded multilinear forms on `ℓ^∞` of arbitrary arity, from the one-variable case, and the
Phillips property `TailProperty` used in the main theorem.
-/
import AltCounter.PhillipsOne

namespace AltCounter

open BoundedContinuousFunction Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A function of `d` arguments in `ℓ^∞` which is additive and homogeneous in each argument and bounded. -/
structure IsBddML {d : ℕ} (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ) : Prop where
  add : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜),
    Φ (Function.update u j (v + w)) = Φ (Function.update u j v) + Φ (Function.update u j w)
  smul : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (c : 𝕜) (v : Linf 𝕜),
    Φ (Function.update u j (c • v)) = c * Φ (Function.update u j v)
  bound : ∀ u : Fin d → Linf 𝕜, ‖Φ u‖ ≤ C * ∏ j, ‖u j‖

variable [IsUltrametricDist 𝕜] [CompleteSpace 𝕜]

/-- Tails of bounded multilinear forms of any arity. -/
theorem tail_multilinear (h : NSC 𝕜) : ∀ (d : ℕ) (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε := by
  sorry

/-- The Phillips property used in the main theorem. -/
theorem tailProperty_of_NSC (h : NSC 𝕜) : TailProperty 𝕜 := by
  sorry

end AltCounter
