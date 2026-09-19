/-
Ultrametric bounds for determinants: stability under small perturbations, and smallness of the determinant
of a matrix that is close to a matrix of small rank.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Basic
import AltCounter.Defs

namespace AltCounter

open Finset Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] {N : ℕ}

/-- Ultrametric Hadamard-type bound. -/
theorem norm_det_le_prod (A : Matrix (Fin N) (Fin N) 𝕜) (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hA : ∀ i j, ‖A i j‖ ≤ c i) : ‖A.det‖ ≤ ∏ i, c i := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Finset.prod_nonneg fun i _ => hc i) ?_
  intro σ _
  have hsign : ‖(Equiv.Perm.sign σ) • (∏ i, A (σ i) i)‖ = ‖∏ i, A (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hsign, norm_prod]
  calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, c (σ i) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA (σ i) i)
    _ = ∏ i, c i := Equiv.prod_comp σ c

/-- The matrix whose `b`-th column is taken from `G` when `b ∈ S` and from `E` otherwise. -/
def mixCols (G E : Matrix (Fin N) (Fin N) 𝕜) (S : Finset (Fin N)) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun a b => if b ∈ S then G a b else E a b

omit [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] in
@[simp] theorem mixCols_apply (G E : Matrix (Fin N) (Fin N) 𝕜) (S : Finset (Fin N)) (a b) :
    mixCols G E S a b = if b ∈ S then G a b else E a b := rfl

omit [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] in
@[simp] theorem mixCols_univ (G E : Matrix (Fin N) (Fin N) 𝕜) : mixCols G E Finset.univ = G := by
  ext a b; simp [mixCols]

omit [IsUltrametricDist 𝕜] in
/-- The multilinear expansion of `det (G + E)` over the subsets of columns taken from `G`. -/
theorem det_add_eq_sum_mixCols (G E : Matrix (Fin N) (Fin N) 𝕜) :
    (G + E).det = ∑ S : Finset (Fin N), (mixCols G E S).det := by
  classical
  have key : ∀ σ : Equiv.Perm (Fin N), ∀ S : Finset (Fin N),
      (∏ i ∈ S, G (σ i) i) * ∏ i ∈ Finset.univ \ S, E (σ i) i
        = ∏ i, mixCols G E S (σ i) i := by
    intro σ S
    rw [← Finset.prod_sdiff (Finset.subset_univ S), mul_comm (∏ i ∈ S, G (σ i) i)]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
      simp [mixCols, hiS]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [mixCols, hi]
  rw [Matrix.det_apply]
  have step : ∀ σ : Equiv.Perm (Fin N),
      (Equiv.Perm.sign σ) • ∏ i, (G + E) (σ i) i
        = ∑ S : Finset (Fin N), (Equiv.Perm.sign σ) • ∏ i, mixCols G E S (σ i) i := by
    intro σ
    have : ∏ i, (G + E) (σ i) i = ∑ S : Finset (Fin N), ∏ i, mixCols G E S (σ i) i := by
      have h1 : ∏ i, (G + E) (σ i) i = ∏ i ∈ Finset.univ, (G (σ i) i + E (σ i) i) := by
        simp [Matrix.add_apply]
      rw [h1, Finset.prod_add, Finset.powerset_univ]
      exact Finset.sum_congr rfl fun S _ => key σ S
    rw [this, Finset.smul_sum]
  simp only [step]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => (Matrix.det_apply _).symm

/-- Entrywise bound for the determinant of a mixed matrix. -/
theorem norm_det_mixCols_le (G E : Matrix (Fin N) (Fin N) 𝕜) (C ε : ℝ) (hC0 : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hG : ∀ i j, ‖G i j‖ ≤ C) (hE : ∀ i j, ‖E i j‖ ≤ ε) (S : Finset (Fin N)) :
    ‖(mixCols G E S).det‖ ≤ C ^ S.card * ε ^ (N - S.card) := by
  classical
  rw [← Matrix.det_transpose]
  have hb : ‖(mixCols G E S)ᵀ.det‖ ≤ ∏ b, (if b ∈ S then C else ε) := by
    refine norm_det_le_prod _ _ (fun b => by split <;> assumption) ?_
    intro b a
    simp only [Matrix.transpose_apply, mixCols_apply]
    split
    · exact hG a b
    · exact hE a b
  refine hb.trans (le_of_eq ?_)
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have e1 : ∀ b ∈ Finset.univ \ S, (if b ∈ S then C else ε) = ε := by
    intro b hb; simp [(Finset.mem_sdiff.mp hb).2]
  have e2 : ∀ b ∈ S, (if b ∈ S then C else ε) = C := by
    intro b hb; simp [hb]
  have h1 : ∏ b ∈ Finset.univ \ S, (if b ∈ S then C else ε) = ε ^ (N - S.card) := by
    rw [Finset.prod_congr rfl e1, Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
  have h2 : ∏ b ∈ S, (if b ∈ S then C else ε) = C ^ S.card := by
    rw [Finset.prod_congr rfl e2, Finset.prod_const]
  rw [h1, h2, mul_comm]

/-- Stability: if `‖G.det‖ ≥ 1`, the entries of `G` are bounded by `C ≥ 1`, and the entries of `E` by `ε` with
`ε * C ^ (N - 1) < 1`, then `‖(G + E).det‖ ≥ 1`. -/
theorem one_le_norm_det_add (G E : Matrix (Fin N) (Fin N) 𝕜) (C ε : ℝ) (hC : 1 ≤ C) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hG : ∀ i j, ‖G i j‖ ≤ C) (hE : ∀ i j, ‖E i j‖ ≤ ε) (hsmall : ε * C ^ (N - 1) < 1)
    (hdet : 1 ≤ ‖G.det‖) : 1 ≤ ‖(G + E).det‖ := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  -- bound for every term other than `S = univ`
  have hterm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase Finset.univ,
      ‖(mixCols G E S).det‖ ≤ C ^ (N - 1) * ε := by
    intro S hS
    have hSne : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
    have hcard : S.card < N := by
      have : S.card < (Finset.univ : Finset (Fin N)).card :=
        Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ S) hSne)
      simpa using this
    refine (norm_det_mixCols_le G E C ε hC0 hε0 hG hE S).trans ?_
    have h1 : C ^ S.card ≤ C ^ (N - 1) :=
      pow_le_pow_right₀ hC (by omega)
    have h2 : ε ^ (N - S.card) ≤ ε ^ 1 :=
      pow_le_pow_of_le_one hε0 hε1 (by omega)
    rw [pow_one] at h2
    exact mul_le_mul h1 h2 (pow_nonneg hε0 _) (pow_nonneg hC0 _)
  have hsum : ‖∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase Finset.univ,
      (mixCols G E S).det‖ ≤ C ^ (N - 1) * ε :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (pow_nonneg hC0 _) hε0) hterm
  have hsmall' : C ^ (N - 1) * ε < 1 := by rw [mul_comm]; exact hsmall
  have hexp : (G + E).det = G.det + ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase
      Finset.univ, (mixCols G E S).det := by
    rw [det_add_eq_sum_mixCols G E,
      ← Finset.add_sum_erase _ (fun S => (mixCols G E S).det)
        (Finset.mem_univ (Finset.univ : Finset (Fin N))), mixCols_univ]
  by_contra hcon
  rw [not_le] at hcon
  have hG' : ‖G.det‖ < 1 := by
    have : G.det = (G + E).det + (-(∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).erase
        Finset.univ, (mixCols G E S).det)) := by rw [hexp]; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [max_lt_iff, norm_neg]
    exact ⟨hcon, lt_of_le_of_lt hsum hsmall'⟩
  exact absurd hdet (not_le.mpr hG')

/-- If `A` (entries bounded by `C ≥ 1`) is within `η ≤ 1` of a matrix of the form `∑_{k < r} u_k ⊗ v_k`
and `r ≤ N`, then `‖A.det‖ ≤ C ^ r * η ^ (N - r)`. -/
theorem norm_det_le_of_close_to_lowrank (A : Matrix (Fin N) (Fin N) 𝕜) (C η : ℝ) (hC : 1 ≤ C)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ C) (r : ℕ) (hr : r ≤ N)
    (u v : Fin r → Fin N → 𝕜) (hclose : ∀ i j, ‖A i j - ∑ k, u k i * v k j‖ ≤ η) :
    ‖A.det‖ ≤ C ^ r * η ^ (N - r) := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  set R : Matrix (Fin N) (Fin N) 𝕜 := Matrix.of fun i j => ∑ k, u k i * v k j with hR
  set E : Matrix (Fin N) (Fin N) 𝕜 := A - R with hE
  have hAdd : A = R + E := by rw [hE]; abel
  have hEbd : ∀ i j, ‖E i j‖ ≤ η := by
    intro i j
    simpa [hE, hR, Matrix.sub_apply] using hclose i j
  have hRbd : ∀ i j, ‖R i j‖ ≤ C := by
    intro i j
    have : R i j = A i j + (-(E i j)) := by simp [hE, Matrix.sub_apply]
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [max_le_iff, norm_neg]
    exact ⟨hA i j, (hEbd i j).trans (hη1.trans hC)⟩
  -- the terms with more than `r` columns coming from `R` vanish
  have hvanish : ∀ S : Finset (Fin N), r < S.card → (mixCols R E S).det = 0 := by
    intro S hS
    apply Matrix.det_eq_zero_of_not_linearIndependent_cols
    intro hli
    have : Fintype ↥(Set.range u) := Set.Finite.fintype (Set.finite_range u)
    have hli' : LinearIndependent 𝕜
        ((fun b => (mixCols R E S)ᵀ b) ∘ (Subtype.val : {x // x ∈ S} → Fin N)) :=
      hli.comp _ Subtype.val_injective
    have hspan : Set.range ((fun b => (mixCols R E S)ᵀ b) ∘
        (Subtype.val : {x // x ∈ S} → Fin N)) ⊆ ↑(Submodule.span 𝕜 (Set.range u)) := by
      rintro x ⟨b, rfl⟩
      have hb : (b : Fin N) ∈ S := b.2
      have hx : (fun b => (mixCols R E S)ᵀ b) (b : Fin N) = ∑ k, (v k (b : Fin N)) • u k := by
        funext a
        simp only [Matrix.transpose_apply, mixCols_apply, hb, hR, Matrix.of_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      simp only [Function.comp_apply, hx, SetLike.mem_coe]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
    have hcard := linearIndependent_le_span' _ hli' (Set.range u) hspan
    rw [Cardinal.mk_coe_finset] at hcard
    have : S.card ≤ Fintype.card ↥(Set.range u) := by exact_mod_cast hcard
    have hle : Fintype.card ↥(Set.range u) ≤ r := by
      simpa using Fintype.card_range_le u
    omega
  -- bound for every term
  have hterm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin N))),
      ‖(mixCols R E S).det‖ ≤ C ^ r * η ^ (N - r) := by
    intro S _
    rcases le_or_gt S.card r with hle | hgt
    · refine (norm_det_mixCols_le R E C η hC0 hη0 hRbd hEbd S).trans ?_
      have h1 : C ^ S.card ≤ C ^ r := pow_le_pow_right₀ hC hle
      have h2 : η ^ (N - S.card) ≤ η ^ (N - r) := pow_le_pow_of_le_one hη0 hη1 (by omega)
      exact mul_le_mul h1 h2 (pow_nonneg hη0 _) (pow_nonneg hC0 _)
    · rw [hvanish S hgt, norm_zero]
      exact mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hη0 _)
  rw [hAdd, det_add_eq_sum_mixCols R E]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hη0 _)) hterm

end AltCounter
