/-
A polynomial over an ultrametric field with infinite residue field that has a coefficient of norm `≥ 1`
takes a value of norm `≥ 1` somewhere on the unit polydisc.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange
import AltCounter.Defs

namespace AltCounter

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜]

/-! ### Polynomials with integral coefficients -/

/-- All coefficients of `p` have norm at most `1`. -/
def IsIntPoly (p : Polynomial 𝕜) : Prop := ∀ n, ‖p.coeff n‖ ≤ 1

omit [IsUltrametricDist 𝕜] in
theorem isIntPoly_one : IsIntPoly (1 : Polynomial 𝕜) := by
  intro n
  rw [Polynomial.coeff_one]
  split <;> simp

theorem IsIntPoly.mul {p q : Polynomial 𝕜} (hp : IsIntPoly p) (hq : IsIntPoly q) :
    IsIntPoly (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro x _
  rw [norm_mul]
  exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [IsUltrametricDist 𝕜] in
theorem IsIntPoly.C_mul {c : 𝕜} (hc : ‖c‖ ≤ 1) {p : Polynomial 𝕜} (hp : IsIntPoly p) :
    IsIntPoly (Polynomial.C c * p) := by
  intro n
  rw [Polynomial.coeff_C_mul, norm_mul]
  exact (mul_le_mul hc (hp _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [IsUltrametricDist 𝕜] in
theorem isIntPoly_X_sub_C {t : 𝕜} (ht : ‖t‖ ≤ 1) :
    IsIntPoly (Polynomial.X - Polynomial.C t : Polynomial 𝕜) := by
  intro n
  rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  match n with
  | 0 => simpa using ht
  | 1 => simp
  | (n + 2) => simp

theorem isIntPoly_prod {ι : Type*} (s : Finset ι) (g : ι → Polynomial 𝕜)
    (h : ∀ i ∈ s, IsIntPoly (g i)) : IsIntPoly (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isIntPoly_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### The one-variable statement -/

/-- One-variable case. -/
theorem exists_unit_eval_poly (hres : InfiniteResidue 𝕜) (f : Polynomial 𝕜) (k : ℕ)
    (hk : 1 ≤ ‖f.coeff k‖) : ∃ t : 𝕜, ‖t‖ ≤ 1 ∧ 1 ≤ ‖f.eval t‖ := by
  classical
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_le] at hcon
  obtain ⟨t, ht1, ht2⟩ := hres (f.natDegree + 1)
  have hinj : Set.InjOn t ↑(Finset.univ : Finset (Fin (f.natDegree + 1))) := by
    intro i _ j _ hij
    by_contra hne
    have h1 := ht2 i j hne
    rw [hij, sub_self, norm_zero] at h1
    exact zero_ne_one h1
  have hdeg : f.degree < (Finset.univ : Finset (Fin (f.natDegree + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast Nat.lt_succ_self f.natDegree)
  have hbasis : ∀ i : Fin (f.natDegree + 1),
      IsIntPoly (Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i) := by
    intro i
    rw [Lagrange.basis]
    refine isIntPoly_prod _ _ fun j hj => ?_
    have hji : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    rw [Lagrange.basisDivisor]
    refine IsIntPoly.C_mul ?_ (isIntPoly_X_sub_C (ht1 j))
    rw [norm_inv, ht2 i j hji, inv_one]
  have hf := Lagrange.eq_interpolate (v := t) hinj hdeg
  have hcoeff : f.coeff k =
      ∑ i : Fin (f.natDegree + 1), f.eval (t i) *
        (Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i).coeff k := by
    conv_lhs => rw [hf]
    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul]
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Fin (f.natDegree + 1)))
    (fun i => f.eval (t i) *
      (Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i).coeff k)
  have hlt : ‖f.coeff k‖ < 1 := by
    rw [hcoeff]
    calc ‖∑ i : Fin (f.natDegree + 1), f.eval (t i) *
            (Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i).coeff k‖
        ≤ ‖f.eval (t i) *
            (Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i).coeff k‖ := hi
      _ = ‖f.eval (t i)‖ *
            ‖(Lagrange.basis (Finset.univ : Finset (Fin (f.natDegree + 1))) t i).coeff k‖ :=
          norm_mul _ _
      _ ≤ ‖f.eval (t i)‖ * 1 := by
          gcongr
          exact hbasis i k
      _ = ‖f.eval (t i)‖ := mul_one _
      _ < 1 := hcon _ (ht1 i)
  linarith

/-! ### Several variables -/

private theorem exists_unit_eval_fin (hres : InfiniteResidue 𝕜) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) 𝕜) (m : Fin n →₀ ℕ), 1 ≤ ‖f.coeff m‖ →
      ∃ z : Fin n → 𝕜, (∀ i, ‖z i‖ ≤ 1) ∧ 1 ≤ ‖eval z f‖ := by
  intro n
  induction n with
  | zero =>
    intro f m hm
    have hm0 : m = 0 := by ext i; exact i.elim0
    subst hm0
    obtain ⟨a, rfl⟩ : ∃ a : 𝕜, f = MvPolynomial.C a := by
      refine ⟨f.coeff 0, ?_⟩
      have := (MvPolynomial.isEmptyRingEquiv 𝕜 (Fin 0)).symm_apply_apply f
      rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero,
        MvPolynomial.isEmptyRingEquiv_symm_apply] at this
      exact this.symm
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [MvPolynomial.eval_C]
    simpa using hm
  | succ n ih =>
    intro f m hm
    have hc : (Polynomial.coeff (MvPolynomial.finSuccEquiv 𝕜 n f) (m 0)).coeff
        (Finsupp.tail m) = f.coeff m := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
    obtain ⟨z', hz'1, hz'2⟩ := ih (Polynomial.coeff (MvPolynomial.finSuccEquiv 𝕜 n f) (m 0))
      (Finsupp.tail m) (by rw [hc]; exact hm)
    have hpc : (Polynomial.map (MvPolynomial.eval z')
        (MvPolynomial.finSuccEquiv 𝕜 n f)).coeff (m 0) =
        MvPolynomial.eval z' (Polynomial.coeff (MvPolynomial.finSuccEquiv 𝕜 n f) (m 0)) := by
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy1, hy2⟩ := exists_unit_eval_poly hres
      (Polynomial.map (MvPolynomial.eval z') (MvPolynomial.finSuccEquiv 𝕜 n f)) (m 0)
      (by rw [hpc]; exact hz'2)
    refine ⟨Fin.cons y z', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hy1
      · intro j; simpa using hz'1 j
    · rw [MvPolynomial.eval_eq_eval_mv_eval']
      exact hy2

/-- Several variables. -/
theorem exists_unit_eval {σ : Type*} [Fintype σ] (hres : InfiniteResidue 𝕜) (f : MvPolynomial σ 𝕜)
    (m : σ →₀ ℕ) (hm : 1 ≤ ‖f.coeff m‖) :
    ∃ z : σ → 𝕜, (∀ i, ‖z i‖ ≤ 1) ∧ 1 ≤ ‖eval z f‖ := by
  classical
  let e := Fintype.equivFin σ
  have hcoeff : (MvPolynomial.rename e f).coeff (Finsupp.mapDomain e m) = f.coeff m :=
    MvPolynomial.coeff_rename_mapDomain _ e.injective f m
  obtain ⟨z, hz1, hz2⟩ := exists_unit_eval_fin hres _ (MvPolynomial.rename e f)
    (Finsupp.mapDomain e m) (by rw [hcoeff]; exact hm)
  refine ⟨fun i => z (e i), fun i => hz1 _, ?_⟩
  rw [MvPolynomial.eval_rename] at hz2
  exact hz2

end AltCounter
