/-
Non-spherical completeness, in the concrete form "there is a decreasing sequence of closed balls with strictly
decreasing radii and empty intersection", implies `NSC` (i.e. `(ℓ^∞ / c₀)' = 0`). This is the direction of
van der Put's theorem that the counterexample needs.
-/
import AltCounter.Phillips

namespace AltCounter

open BoundedContinuousFunction

/-- A normed field is *not spherically complete*, witnessed concretely: closed balls `B(c n, r n)` that are nested
(`‖c (n+1) - c n‖ ≤ r n` and `r` strictly decreasing) with empty intersection. -/
def HasEmptyNestedBalls (𝕜 : Type*) [NormedField 𝕜] : Prop :=
  ∃ (c : ℕ → 𝕜) (r : ℕ → ℝ), StrictAnti r ∧ (∀ n, ‖c (n + 1) - c n‖ ≤ r n) ∧
    ∀ a : 𝕜, ∃ n, r n < ‖a - c n‖

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜]

/-! ### The (missing) ultrametric inequality on `ℓ^∞`

`ℕ →ᵇ 𝕜` carries no `IsUltrametricDist` instance, but the inequality itself is immediate coordinatewise. -/

theorem Linf.norm_add_le_max (f g : Linf 𝕜) : ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  refine (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg f))).mpr fun i => ?_
  refine le_trans ?_ (max_le_max (f.norm_coe_le_norm i) (g.norm_coe_le_norm i))
  exact IsUltrametricDist.norm_add_le_max (f i) (g i)

/-- If `𝕜` is not spherically complete then every continuous linear functional on `ℓ^∞` that vanishes on the standard
basis vectors is zero. -/
theorem nsc_of_hasEmptyNestedBalls (h : HasEmptyNestedBalls 𝕜) : NSC 𝕜 := by
  obtain ⟨c, r, hr, hcr, hempty⟩ := h
  intro φ hφ
  by_contra hne
  have hA : 0 < ‖φ‖ := by
    rcases lt_or_eq_of_le (norm_nonneg φ) with h | h
    · exact h
    · refine absurd (ContinuousLinearMap.ext fun z => ?_) hne
      have h1 : ‖φ z‖ ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm z
      rw [← h, zero_mul] at h1
      simpa using norm_le_zero_iff.mp h1
  -- the radii are positive
  have hrpos : ∀ n, 0 < r n := fun n =>
    lt_of_le_of_lt ((norm_nonneg _).trans (hcr (n + 1))) (hr (Nat.lt_succ_self n))
  -- `φ` kills the "head" of any vector, hence only sees tails
  have hhead : ∀ (M : ℕ) (z : Linf 𝕜), φ (headOf M z) = 0 := by
    intro M z
    rw [headOf_eq_sum, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hφ i, smul_zero]
  have htail : ∀ (M : ℕ) (z : Linf 𝕜), φ z = φ (tailOf M z) := by
    intro M z
    conv_lhs => rw [← headOf_add_tailOf M z]
    rw [map_add, hhead, zero_add]
  -- almost-norming vectors: `φ w = 1` with `‖w‖` close to `1/‖φ‖`
  have hunit : ∀ t : ℝ, 0 < t → t < ‖φ‖ → ∃ w : Linf 𝕜, φ w = 1 ∧ ‖w‖ ≤ 1 / t := by
    intro t ht htA
    have hex : ∃ z : Linf 𝕜, t * ‖z‖ < ‖φ z‖ := by
      by_contra hcon
      exact absurd (φ.opNorm_le_bound ht.le fun z => not_lt.mp fun hlt => hcon ⟨z, hlt⟩)
        (not_le.mpr htA)
    obtain ⟨z, hz⟩ := hex
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hfz : 0 < ‖φ z‖ := lt_of_le_of_lt (by positivity) hz
    have hfz0 : φ z ≠ 0 := norm_pos_iff.mp hfz
    refine ⟨(φ z)⁻¹ • z, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hfz0]
    · rw [norm_smul, norm_inv, show ‖φ z‖⁻¹ * ‖z‖ = ‖z‖ / ‖φ z‖ by ring,
        div_le_div_iff₀ hfz ht]
      linarith [mul_comm t ‖z‖]
  -- the increments
  have key : ∀ n : ℕ, ∃ s : Linf 𝕜, φ s = c (n + 1 + 1) - c (n + 1) ∧ ‖s‖ ≤ r n / ‖φ‖ := by
    intro n
    have hrn := hrpos n
    have hrn1 := hrpos (n + 1)
    have hlt : r (n + 1) < r n := hr (Nat.lt_succ_self n)
    have h1 : (0 : ℝ) < ‖φ‖ * r (n + 1) / r n := by positivity
    have h2 : ‖φ‖ * r (n + 1) / r n < ‖φ‖ := by
      rw [div_lt_iff₀ hrn]
      nlinarith
    obtain ⟨w, hw1, hw2⟩ := hunit _ h1 h2
    rw [one_div_div] at hw2
    refine ⟨(c (n + 1 + 1) - c (n + 1)) • w, ?_, ?_⟩
    · rw [map_smul, hw1, smul_eq_mul, mul_one]
    · rw [norm_smul]
      have hstep : ‖c (n + 1 + 1) - c (n + 1)‖ * ‖w‖ ≤ r (n + 1) * (r n / (‖φ‖ * r (n + 1))) :=
        mul_le_mul (hcr (n + 1)) hw2 (norm_nonneg _) hrn1.le
      refine hstep.trans_eq ?_
      field_simp
  choose s hs1 hs2 using key
  -- the approximating sequence
  obtain ⟨w₀, hw₀, -⟩ := hunit (‖φ‖ / 2) (by linarith) (by linarith)
  obtain ⟨x, hx0, hxs⟩ :
      ∃ x : ℕ → Linf 𝕜, x 0 = c 1 • w₀ ∧ ∀ n, x (n + 1) = x n + s n :=
    ⟨fun n => c 1 • w₀ + ∑ k ∈ Finset.range n, s k, by simp, by
      intro n; simp [Finset.sum_range_succ, add_assoc]⟩
  have hφx : ∀ n, φ (x n) = c (n + 1) := by
    intro n
    induction n with
    | zero => rw [hx0, map_smul, hw₀, smul_eq_mul, mul_one]
    | succ n ih => rw [hxs n, map_add, ih, hs1 n]; abel
  -- the sequence is "Cauchy with explicit rate"
  have hdiff : ∀ n d : ℕ, ‖x (n + d) - x n‖ ≤ r n / ‖φ‖ := by
    intro n d
    induction d with
    | zero => simpa using div_nonneg (hrpos n).le hA.le
    | succ d ih =>
      have hrw : x (n + (d + 1)) - x n = s (n + d) + (x (n + d) - x n) := by
        rw [show n + (d + 1) = n + d + 1 from rfl, hxs (n + d)]; abel
      rw [hrw]
      refine (Linf.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hs2 (n + d)).trans ((div_le_div_iff_of_pos_right hA).mpr
        (hr.antitone (Nat.le_add_right n d)))
  -- the diagonal vector
  have hxi : ∀ i, ‖x i‖ ≤ max (r 0 / ‖φ‖) ‖x 0‖ := by
    intro i
    have h1 : x i = (x (0 + i) - x 0) + x 0 := by rw [zero_add]; abel
    rw [h1]
    exact (Linf.norm_add_le_max _ _).trans (max_le_max (hdiff 0 i) le_rfl)
  obtain ⟨y, hy⟩ : ∃ y : Linf 𝕜, ∀ i, y i = x i i :=
    ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => x i i)
      (max (r 0 / ‖φ‖) ‖x 0‖) (fun i => ((x i).norm_coe_le_norm i).trans (hxi i)), fun _ => rfl⟩
  -- the tail estimate
  have htailbd : ∀ n, ‖tailOf n (y - x n)‖ ≤ r n / ‖φ‖ := by
    intro n
    have hnn : (0 : ℝ) ≤ r n / ‖φ‖ := div_nonneg (hrpos n).le hA.le
    refine (BoundedContinuousFunction.norm_le hnn).mpr fun i => ?_
    rw [tailOf_apply]
    split_ifs with hi
    · simpa using hnn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
      have hcoord : (y - x n) (n + d) = (x (n + d) - x n) (n + d) := by
        simp only [BoundedContinuousFunction.sub_apply, hy]
      rw [hcoord]
      exact ((x (n + d) - x n).norm_coe_le_norm (n + d)).trans (hdiff n d)
  -- `φ y` lies in every ball
  have hclose : ∀ n, ‖φ y - c (n + 1)‖ ≤ r n := by
    intro n
    have h1 : φ y - c (n + 1) = φ (y - x n) := by rw [map_sub, hφx n]
    rw [h1, htail n (y - x n)]
    calc ‖φ (tailOf n (y - x n))‖ ≤ ‖φ‖ * ‖tailOf n (y - x n)‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (r n / ‖φ‖) := by
          exact mul_le_mul_of_nonneg_left (htailbd n) hA.le
      _ = r n := by field_simp
  have hclose' : ∀ n, ‖φ y - c n‖ ≤ r n := by
    intro n
    have h1 : φ y - c n = (φ y - c (n + 1)) + (c (n + 1) - c n) := by abel
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hclose n) (hcr n))
  obtain ⟨m, hm⟩ := hempty (φ y)
  exact absurd (hclose' m) (not_le.mpr hm)

end AltCounter
