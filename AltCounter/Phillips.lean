/-
The multilinear Phillips (tail) property from the classical characterisation of non-spherically-complete
fields: `(ℓ^∞ / c₀)' = 0`, i.e. every continuous linear functional on `ℓ^∞` that kills all the unit vectors is `0`
(van der Put 1969, Thm 3.2: this holds iff the field is not spherically complete).
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import AltCounter.FiniteLemma

namespace AltCounter

open BoundedContinuousFunction Filter Topology

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- The `i`-th unit vector of `ℓ^∞`. -/
noncomputable def basisVec (i : ℕ) : Linf 𝕜 := blockVec i (fun _ : Fin 1 => (1 : 𝕜))

/-- `(ℓ^∞ / c₀)' = 0`: a continuous linear functional on `ℓ^∞` vanishing on all unit vectors is zero.
For a complete non-archimedean field this is equivalent to: the field is not spherically complete. -/
def NSC : Prop := ∀ φ : Linf 𝕜 →L[𝕜] 𝕜, (∀ i, φ (basisVec 𝕜 i) = 0) → φ = 0

variable {𝕜}

/-- A function of `d` arguments in `ℓ^∞` which is additive and homogeneous in each argument and bounded. -/
structure IsBddML {d : ℕ} (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ) : Prop where
  add : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜),
    Φ (Function.update u j (v + w)) = Φ (Function.update u j v) + Φ (Function.update u j w)
  smul : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (c : 𝕜) (v : Linf 𝕜),
    Φ (Function.update u j (c • v)) = c * Φ (Function.update u j v)
  bound : ∀ u : Fin d → Linf 𝕜, ‖Φ u‖ ≤ C * ∏ j, ‖u j‖

variable [IsUltrametricDist 𝕜] [CompleteSpace 𝕜]

/-- Shift trick: under `NSC`, the values of a functional on the unit vectors tend to `0`. -/
theorem tendsto_apply_basisVec (h : NSC 𝕜) (φ : Linf 𝕜 →L[𝕜] 𝕜) :
    Tendsto (fun i => φ (basisVec 𝕜 i)) atTop (𝓝 0) := by
  sorry

/-- Tails of a functional: uniform smallness on unit vectors supported far out. -/
theorem tail_functional (h : NSC 𝕜) (φ : Linf 𝕜 →L[𝕜] 𝕜) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : Linf 𝕜, ‖x‖ ≤ 1 → (∀ i < N, x i = 0) → ‖φ x‖ ≤ ε := by
  sorry

/-- Tails of bounded multilinear forms of any arity. -/
theorem tail_multilinear (h : NSC 𝕜) : ∀ (d : ℕ) (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε := by
  sorry

/-- The Phillips property used in the main theorem. -/
theorem tailProperty_of_NSC (h : NSC 𝕜) : TailProperty 𝕜 := by
  sorry

end AltCounter
