/-
Determinants of symmetric zero-diagonal matrices in characteristic 2 as sums of squares over perfect matchings.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

namespace AltCounter

set_option linter.unusedSectionVars false

open Finset

variable {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Perfect matchings of `α`, encoded as fixed-point-free involutions. -/
def PM (α : Type*) [Fintype α] [DecidableEq α] : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

/-- The product of the entries of `B` over the edges `{i, σ i}`, `i < σ i`, of a matching. -/
def pfTerm (B : Matrix α α R) (σ : Equiv.Perm α) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), B i (σ i)

/-! ### Helper lemmas -/

theorem mem_PM {σ : Equiv.Perm α} : σ ∈ PM α ↔ σ * σ = 1 ∧ ∀ i, σ i ≠ i := by
  simp [PM]

theorem inv_eq_self_iff_sq_eq_one {σ : Equiv.Perm α} : σ⁻¹ = σ ↔ σ * σ = 1 := by
  constructor
  · intro h
    nth_rewrite 1 [← h]
    exact inv_mul_cancel σ
  · intro h
    exact inv_eq_of_mul_eq_one_right h

theorem apply_apply_of_sq_eq_one {σ : Equiv.Perm α} (hinv : σ * σ = 1) (i : α) :
    σ (σ i) = i := by
  rw [← Equiv.Perm.mul_apply, hinv, Equiv.Perm.one_apply]

/-- In characteristic two the sign of a permutation casts to `1`. -/
theorem cast_sign_eq_one [CharP R 2] (σ : Equiv.Perm α) :
    ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · norm_num
  · push_cast
    exact CharTwo.neg_eq 1

/-- The Leibniz formula in characteristic two: all signs disappear. -/
theorem det_eq_sum_prod [CharP R 2] (B : Matrix α α R) :
    B.det = ∑ σ : Equiv.Perm α, ∏ i, B (σ i) i := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cast_sign_eq_one σ, one_mul]

/-- Reindexing: the Leibniz term of `σ⁻¹` equals that of `σ` when `B` is symmetric. -/
theorem prod_inv_perm (B : Matrix α α R) (hsymm : ∀ i j, B i j = B j i) (σ : Equiv.Perm α) :
    ∏ i, B (σ⁻¹ i) i = ∏ i, B (σ i) i := by
  calc ∏ i, B (σ⁻¹ i) i
      = ∏ i, B (σ⁻¹ (σ i)) (σ i) := (Equiv.prod_comp σ (fun i => B (σ⁻¹ i) i)).symm
    _ = ∏ i, B i (σ i) := by simp
    _ = ∏ i, B (σ i) i := Finset.prod_congr rfl fun i _ => hsymm i (σ i)

/-- A permutation with a fixed point contributes `0` when the diagonal of `B` vanishes. -/
theorem prod_eq_zero_of_fixed (B : Matrix α α R) (hdiag : ∀ i, B i i = 0)
    {σ : Equiv.Perm α} {i : α} (hi : σ i = i) : ∏ j, B (σ j) j = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hdiag])

/-- In characteristic two only the involutions survive in the Leibniz formula. -/
theorem sum_perm_eq_sum_involutions [CharP R 2] (B : Matrix α α R)
    (hsymm : ∀ i j, B i j = B j i) :
    ∑ σ : Equiv.Perm α, (∏ i, B (σ i) i)
      = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ * σ = 1), ∏ i, B (σ i) i := by
  have hzero :
      ∑ σ ∈ Finset.univ \ Finset.univ.filter (fun σ : Equiv.Perm α => σ * σ = 1),
        (∏ i, B (σ i) i) = 0 := by
    refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      rw [prod_inv_perm B hsymm σ]
      exact CharTwo.add_self_eq_zero _
    · intro σ hσ _ hcon
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hσ
      exact hσ (inv_eq_self_iff_sq_eq_one.mp hcon)
    · intro σ hσ
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hσ ⊢
      intro hcon
      refine hσ ?_
      rw [← mul_inv_rev] at hcon
      exact inv_eq_one.mp hcon
    · intro σ _
      exact inv_inv σ
  rw [← Finset.sum_sdiff
    (Finset.filter_subset (fun σ : Equiv.Perm α => σ * σ = 1) Finset.univ), hzero, zero_add]

/-- For a fixed-point-free involution the Leibniz term is the square of the matching product. -/
theorem prod_eq_pfTerm_sq (B : Matrix α α R) (hsymm : ∀ i j, B i j = B j i)
    {σ : Equiv.Perm α} (hσ : σ ∈ PM α) :
    ∏ i, B (σ i) i = (pfTerm B σ) ^ 2 := by
  obtain ⟨hinv, hfix⟩ := mem_PM.mp hσ
  have hσσ : ∀ i, σ (σ i) = i := apply_apply_of_sq_eq_one hinv
  have key := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i < σ i)
      (fun i => B (σ i) i)
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), B (σ i) i = pfTerm B σ :=
    Finset.prod_congr rfl fun i _ => hsymm _ _
  have h2 : pfTerm B σ = ∏ i ∈ Finset.univ.filter (fun i => ¬ i < σ i), B (σ i) i := by
    unfold pfTerm
    refine Finset.prod_nbij' (fun i => σ i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hσσ]
      exact not_lt.mpr (le_of_lt ha)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hσσ]
      exact lt_of_le_of_ne (not_lt.mp ha) (hfix a)
    · intro a _
      exact hσσ a
    · intro a _
      exact hσσ a
    · intro a _
      rw [hσσ]
  rw [← key, h1, ← h2, sq]

/-- In characteristic 2 the determinant of a symmetric matrix with zero diagonal is the sum over perfect
matchings of the squares of the matching products (so it is the square of the "Pfaffian"). -/
theorem det_eq_sum_PM_sq [CharP R 2] (B : Matrix α α R) (hsymm : ∀ i j, B i j = B j i)
    (hdiag : ∀ i, B i i = 0) : B.det = ∑ σ ∈ PM α, (pfTerm B σ) ^ 2 := by
  have hsub : PM α ⊆ Finset.univ.filter (fun σ : Equiv.Perm α => σ * σ = 1) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_PM.mp hσ).1
  have hvanish : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ * σ = 1), σ ∉ PM α →
      (∏ i, B (σ i) i) = 0 := by
    intro σ hσ hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [mem_PM, not_and_or] at hnot
    rcases hnot with h | h
    · exact absurd hσ h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero_of_fixed B hdiag hi
  rw [det_eq_sum_prod B, sum_perm_eq_sum_involutions B hsymm,
    ← Finset.sum_subset hsub hvanish]
  exact Finset.sum_congr rfl fun σ hσ => prod_eq_pfTerm_sq B hsymm hσ

/-! ### Counting perfect matchings -/

/-- The matrix with `0` on the diagonal and `1` everywhere else, over `ZMod 2`. -/
def offDiagOne (α : Type*) [Fintype α] [DecidableEq α] : Matrix α α (ZMod 2) :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem offDiagOne_symm (i j : α) : offDiagOne α i j = offDiagOne α j i := by
  simp only [offDiagOne, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem offDiagOne_diag (i : α) : offDiagOne α i i = 0 := by
  simp [offDiagOne]

theorem offDiagOne_of_ne {i j : α} (h : i ≠ j) : offDiagOne α i j = 1 := by
  simp [offDiagOne, h]

theorem pfTerm_offDiagOne {σ : Equiv.Perm α} (hσ : σ ∈ PM α) :
    pfTerm (offDiagOne α) σ = 1 := by
  obtain ⟨-, hfix⟩ := mem_PM.mp hσ
  unfold pfTerm
  refine Finset.prod_eq_one fun i _ => ?_
  exact offDiagOne_of_ne (Ne.symm (hfix i))

theorem det_offDiagOne : (offDiagOne α).det = ((PM α).card : ZMod 2) := by
  rw [det_eq_sum_PM_sq (offDiagOne α) offDiagOne_symm offDiagOne_diag]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ZMod 2))
    (fun σ hσ => by rw [pfTerm_offDiagOne hσ, one_pow])]
  simp

theorem offDiagOne_mul_self (h : Even (Fintype.card α)) :
    offDiagOne α * offDiagOne α = 1 := by
  have hcard : ((Fintype.card α : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    exact h
  ext i j
  have hstep : (offDiagOne α * offDiagOne α) i j
      = ((Finset.univ \ ({i, j} : Finset α)).card : ZMod 2) := by
    rw [Matrix.mul_apply, ← Finset.sum_sdiff (Finset.subset_univ ({i, j} : Finset α))]
    have hz : ∑ k ∈ ({i, j} : Finset α), offDiagOne α i k * offDiagOne α k j = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rw [offDiagOne_diag, zero_mul]
      · rw [offDiagOne_diag, mul_zero]
    have ho : ∑ k ∈ Finset.univ \ ({i, j} : Finset α), offDiagOne α i k * offDiagOne α k j
        = ((Finset.univ \ ({i, j} : Finset α)).card : ZMod 2) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ZMod 2)) ?_]
      · simp
      · intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and, not_or] at hk
        rw [offDiagOne_of_ne (Ne.symm hk.1), offDiagOne_of_ne hk.2, one_mul]
    rw [hz, ho, add_zero]
  have hcomp : ((Finset.univ \ ({i, j} : Finset α)).card : ZMod 2)
      = ((({i, j} : Finset α)).card : ZMod 2) := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({i, j} : Finset α))
    have h2 : (((Finset.univ \ ({i, j} : Finset α)).card + ({i, j} : Finset α).card : ℕ) : ZMod 2)
        = 0 := by
      rw [this, Finset.card_univ, hcard]
    push_cast at h2
    exact CharTwo.add_eq_zero.mp h2
  rw [hstep, hcomp]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    simp
  · rw [Matrix.one_apply_ne hij, Finset.card_insert_of_notMem (by simpa using hij),
      Finset.card_singleton]
    show ((1 + 1 : ℕ) : ZMod 2) = 0
    exact ZMod.natCast_self 2

/-- The number of perfect matchings of a set of even cardinality is odd. -/
theorem card_PM_odd (h : Even (Fintype.card α)) : Odd (PM α).card := by
  have hmul : (offDiagOne α).det * (offDiagOne α).det = 1 := by
    rw [← Matrix.det_mul, offDiagOne_mul_self h, Matrix.det_one]
  rw [det_offDiagOne] at hmul
  rw [← ZMod.natCast_eq_one_iff_odd]
  generalize ((PM α).card : ZMod 2) = x at hmul
  revert hmul
  revert x
  decide

end AltCounter
