/-
The literal form of `(ℓ^∞ / c₀)' = 0` (a continuous functional vanishing on all null sequences is zero) implies `NSC`.
Not used by the main theorems.
-/
import AltCounter.MainNSC

namespace AltCounter

open Filter Topology BoundedContinuousFunction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If every continuous linear functional on `ℓ^∞` that vanishes on `c₀` (the sequences tending to `0`) is zero,
then every continuous linear functional that vanishes on the standard basis vectors is zero. -/
theorem nsc_of_dual
    (hdual : ∀ φ : Linf 𝕜 →L[𝕜] 𝕜,
      (∀ x : Linf 𝕜, Tendsto (fun i => x i) atTop (𝓝 0) → φ x = 0) → φ = 0) : NSC 𝕜 := by
  intro φ hφ
  apply hdual
  intro x hx
  have hhead : ∀ M, φ (headOf M x) = 0 := by
    intro M
    rw [headOf_eq_sum, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hφ, smul_zero]
  have htail : ∀ M, φ x = φ (tailOf M x) := by
    intro M
    conv_lhs => rw [← headOf_add_tailOf M x]
    rw [map_add, hhead, zero_add]
  -- it suffices to show ‖φ x‖ ≤ ‖φ‖ * ε for every ε > 0
  have hle : ∀ ε : ℝ, 0 < ε → ‖φ x‖ ≤ ‖φ‖ * ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hx) ε hε
    have hnorm : ‖tailOf N x‖ ≤ ε := by
      rw [BoundedContinuousFunction.norm_le hε.le]
      intro i
      rw [tailOf_apply]
      split_ifs with hi
      · simpa using hε.le
      · have := hN i (not_lt.1 hi)
        rw [dist_zero_right] at this
        exact this.le
    calc ‖φ x‖ = ‖φ (tailOf N x)‖ := by rw [htail N]
      _ ≤ ‖φ‖ * ‖tailOf N x‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * ε := by gcongr
  have h0 : ‖φ x‖ ≤ 0 := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hpos : 0 < ‖φ‖ + 1 := by positivity
    have := hle (δ / (‖φ‖ + 1)) (by positivity)
    calc ‖φ x‖ ≤ ‖φ‖ * (δ / (‖φ‖ + 1)) := this
      _ < 0 + δ := by
        rw [zero_add, mul_div_assoc']
        rw [div_lt_iff₀ hpos]
        nlinarith [norm_nonneg φ]
  exact norm_le_zero_iff.1 h0

end AltCounter
