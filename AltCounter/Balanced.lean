/-
Multivariate-polynomial lemmas in characteristic 2: coefficients at "balanced" squarefree monomials.
Variables are indexed by `ι ⊕ ι` (`inl i` = `X i`, `inr i` = `Y i`).
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.CharP.Two
import AltCounter.Pfaffian

namespace AltCounter

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The balanced squarefree monomial `∏_{i ∈ S} X_i Y_i`. -/
noncomputable def bal (S : Finset ι) : (ι ⊕ ι) →₀ ℕ :=
  ∑ i ∈ S, (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1)

/-- The monomial `∏_{i ∈ S} x_i ^ 2` in the diagonal variables. -/
noncomputable def dbl (S : Finset ι) : ι →₀ ℕ := ∑ i ∈ S, Finsupp.single i 2

/-- Swap `X ↔ Y`. -/
noncomputable def swapXY : MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial (ι ⊕ ι) R := rename Sum.swap

/-- Substitute `Y_i := X_i`. -/
noncomputable def diagXY : MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial ι R := rename (Sum.elim id id)

/-! ### Elementary helper lemmas -/

section Helpers

omit [Fintype ι] [DecidableEq ι] in
lemma sum_swap_injective : Function.Injective (Sum.swap : ι ⊕ ι → ι ⊕ ι) :=
  Sum.swap_leftInverse.injective

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma swapXY_X (v : ι ⊕ ι) : (swapXY (X v) : MvPolynomial (ι ⊕ ι) R) = X (Sum.swap v) :=
  rename_X _ _

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma diagXY_X (v : ι ⊕ ι) :
    (diagXY (X v) : MvPolynomial ι R) = X (Sum.elim id id v) :=
  rename_X _ _

omit [Fintype ι] in
@[simp] lemma bal_apply_inl (S : Finset ι) (j : ι) :
    bal S (Sum.inl j) = if j ∈ S then 1 else 0 := by
  simp [bal, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [Fintype ι] in
@[simp] lemma bal_apply_inr (S : Finset ι) (j : ι) :
    bal S (Sum.inr j) = if j ∈ S then 1 else 0 := by
  simp [bal, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [Fintype ι] in
@[simp] lemma dbl_apply (S : Finset ι) (j : ι) :
    dbl S j = if j ∈ S then 2 else 0 := by
  simp [dbl, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [Fintype ι] in
lemma bal_apply_le_one (S : Finset ι) (v : ι ⊕ ι) : bal S v ≤ 1 := by
  cases v with
  | inl j => rw [bal_apply_inl]; split <;> simp
  | inr j => rw [bal_apply_inr]; split <;> simp

omit [Fintype ι] in
/-- Applying `Finsupp.mapDomain (Sum.elim id id)` adds the two halves. -/
lemma mapDomain_elim_apply (u : (ι ⊕ ι) →₀ ℕ) (j : ι) :
    (Finsupp.mapDomain (Sum.elim id id) u) j = u (Sum.inl j) + u (Sum.inr j) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [Finsupp.mapDomain_add, Finsupp.add_apply, hf, hg]
      ring
  | single v b =>
      rw [Finsupp.mapDomain_single]
      cases v with
      | inl i => simp [Finsupp.single_apply]
      | inr i => simp [Finsupp.single_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma mapDomain_swap_apply_inl (u : (ι ⊕ ι) →₀ ℕ) (j : ι) :
    (Finsupp.mapDomain Sum.swap u) (Sum.inl j) = u (Sum.inr j) := by
  simpa using Finsupp.mapDomain_apply (M := ℕ) sum_swap_injective u (Sum.inr j)

omit [Fintype ι] [DecidableEq ι] in
lemma mapDomain_swap_apply_inr (u : (ι ⊕ ι) →₀ ℕ) (j : ι) :
    (Finsupp.mapDomain Sum.swap u) (Sum.inr j) = u (Sum.inl j) := by
  simpa using Finsupp.mapDomain_apply (M := ℕ) sum_swap_injective u (Sum.inl j)

omit [Fintype ι] [DecidableEq ι] in
lemma mapDomain_swap_involutive (u : (ι ⊕ ι) →₀ ℕ) :
    Finsupp.mapDomain Sum.swap (Finsupp.mapDomain Sum.swap u) = u := by
  rw [← Finsupp.mapDomain_comp]
  have h : (Sum.swap ∘ Sum.swap : ι ⊕ ι → ι ⊕ ι) = id := funext fun v => Sum.swap_swap v
  rw [h, Finsupp.mapDomain_id]

omit [Fintype ι] in
lemma mapDomain_elim_swap (u : (ι ⊕ ι) →₀ ℕ) :
    Finsupp.mapDomain (Sum.elim id id) (Finsupp.mapDomain Sum.swap u)
      = Finsupp.mapDomain (Sum.elim id id) u := by
  ext j
  rw [mapDomain_elim_apply, mapDomain_elim_apply, mapDomain_swap_apply_inl,
    mapDomain_swap_apply_inr]
  exact Nat.add_comm _ _

omit [Fintype ι] in
lemma mapDomain_swap_bal (S : Finset ι) :
    Finsupp.mapDomain Sum.swap (bal S) = bal S := by
  ext v
  cases v with
  | inl j => rw [mapDomain_swap_apply_inl, bal_apply_inl, bal_apply_inr]
  | inr j => rw [mapDomain_swap_apply_inr, bal_apply_inr, bal_apply_inl]

omit [Fintype ι] in
lemma mapDomain_elim_bal (S : Finset ι) :
    Finsupp.mapDomain (Sum.elim id id) (bal S) = dbl S := by
  ext j
  rw [mapDomain_elim_apply, bal_apply_inl, bal_apply_inr, dbl_apply]
  split <;> simp

/-- The coefficient of a renamed polynomial is the sum of the coefficients in the fibre. -/
lemma coeff_rename_eq_sum {σ τ : Type*} [DecidableEq τ]
    (F : σ → τ) (f : MvPolynomial σ R) (d : τ →₀ ℕ) :
    (rename F f).coeff d
      = ∑ u ∈ f.support, if Finsupp.mapDomain F u = d then f.coeff u else 0 := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [rename_monomial, coeff_monomial]

omit [Fintype ι] in
lemma prod_X_sq_eq_monomial_dbl (S : Finset ι) :
    ∏ i ∈ S, (X i : MvPolynomial ι R) ^ 2 = monomial (dbl S) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [dbl]
  | insert a S ha ih =>
      have hdbl : dbl (insert a S) = Finsupp.single a 2 + dbl S := by
        rw [dbl, dbl, Finset.sum_insert ha]
      rw [Finset.prod_insert ha, ih, X_pow_eq_monomial, monomial_mul_monomial, mul_one, hdbl]

/-! ### Facts about perfect matchings -/

lemma PM_apply_apply {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι) (i : ι) : σ (σ i) = i := by
  simp only [PM, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  have h := congrArg (fun τ : Equiv.Perm ι => τ i) hσ.1
  simpa [Equiv.Perm.mul_apply] using h

lemma PM_apply_ne {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι) (i : ι) : σ i ≠ i := by
  simp only [PM, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  exact hσ.2 i

/-- `σ` maps the "small" half of the edges bijectively onto the "large" half. -/
lemma PM_image_edges [LinearOrder ι] {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι) :
    (Finset.univ.filter (fun i : ι => i < σ i)).image σ
      = Finset.univ.filter (fun i : ι => ¬ (i < σ i)) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [PM_apply_apply hσ i]
    exact not_lt.mpr (le_of_lt hi)
  · intro hj
    refine ⟨σ j, ?_, PM_apply_apply hσ j⟩
    rw [PM_apply_apply hσ j]
    exact lt_of_le_of_ne (not_lt.mp hj) (PM_apply_ne hσ j)

/-- For a perfect matching, `∏_{i < σ i} (F i * F (σ i))` is the product over everything. -/
lemma PM_prod_edges [LinearOrder ι] {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι)
    {M : Type*} [CommMonoid M] (F : ι → M) :
    (∏ i ∈ Finset.univ.filter (fun i : ι => i < σ i), (F i * F (σ i))) = ∏ i : ι, F i := by
  rw [Finset.prod_mul_distrib]
  have h : ∏ i ∈ Finset.univ.filter (fun i : ι => i < σ i), F (σ i)
      = ∏ j ∈ (Finset.univ.filter (fun i : ι => i < σ i)).image σ, F j :=
    (Finset.prod_image (fun x _ y _ h => σ.injective h)).symm
  rw [h, PM_image_edges hσ]
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

lemma PM_card_edges [LinearOrder ι] {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι) :
    2 * (Finset.univ.filter (fun i : ι => i < σ i)).card = Fintype.card ι := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i : ι => i < σ i)
  have h2 : (Finset.univ.filter (fun i : ι => ¬ (i < σ i))).card
      = (Finset.univ.filter (fun i : ι => i < σ i)).card := by
    rw [← PM_image_edges hσ, Finset.card_image_of_injective _ σ.injective]
  rw [h2] at h
  rw [← Finset.card_univ, ← h]
  ring

end Helpers

/-! ### The five theorems -/

/-- For a swap-invariant polynomial in characteristic 2, the coefficient of a balanced monomial can be read
off after the diagonal substitution. -/
theorem coeff_bal_of_swap_invariant [CharP R 2] (f : MvPolynomial (ι ⊕ ι) R) (hf : swapXY f = f)
    (S : Finset ι) : f.coeff (bal S) = (diagXY f).coeff (dbl S) := by
  classical
  have hf' : (rename Sum.swap f : MvPolynomial (ι ⊕ ι) R) = f := hf
  -- the fibre of `dbl S`
  set T : Finset ((ι ⊕ ι) →₀ ℕ) :=
    f.support.filter (fun u => Finsupp.mapDomain (Sum.elim id id) u = dbl S) with hTdef
  have hsum : (diagXY f).coeff (dbl S) = ∑ u ∈ T, f.coeff u := by
    rw [hTdef, Finset.sum_filter]
    exact coeff_rename_eq_sum (Sum.elim id id) f (dbl S)
  -- swapping does not change the coefficient
  have hcoeff : ∀ u : (ι ⊕ ι) →₀ ℕ,
      f.coeff (Finsupp.mapDomain Sum.swap u) = f.coeff u := by
    intro u
    have h := coeff_rename_mapDomain (R := R) Sum.swap sum_swap_injective f u
    rw [hf'] at h
    exact h
  have hmemT : ∀ u ∈ T, Finsupp.mapDomain Sum.swap u ∈ T := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff, hcoeff, ← MvPolynomial.mem_support_iff]
      exact hu1
    · rw [mapDomain_elim_swap]; exact hu2
  -- the only swap-fixed point of the fibre is `bal S`
  have hfix : ∀ u ∈ T, Finsupp.mapDomain Sum.swap u = u → u = bal S := by
    intro u hu hsw
    obtain ⟨-, hu2⟩ := Finset.mem_filter.mp hu
    have hlr : ∀ j : ι, u (Sum.inl j) = u (Sum.inr j) := by
      intro j
      have h := congrArg (fun w : (ι ⊕ ι) →₀ ℕ => w (Sum.inl j)) hsw
      simp only [mapDomain_swap_apply_inl] at h
      exact h.symm
    have hj : ∀ j : ι, u (Sum.inl j) + u (Sum.inr j) = if j ∈ S then 2 else 0 := by
      intro j
      rw [← mapDomain_elim_apply, hu2, dbl_apply]
    ext v
    cases v with
    | inl j =>
        have h1 := hj j
        rw [← hlr j] at h1
        rw [bal_apply_inl]
        by_cases hjS : j ∈ S
        · rw [if_pos hjS]; rw [if_pos hjS] at h1; omega
        · rw [if_neg hjS]; rw [if_neg hjS] at h1; omega
    | inr j =>
        have h1 := hj j
        rw [hlr j] at h1
        rw [bal_apply_inr]
        by_cases hjS : j ∈ S
        · rw [if_pos hjS]; rw [if_pos hjS] at h1; omega
        · rw [if_neg hjS]; rw [if_neg hjS] at h1; omega
  -- the sum over the fibre minus `bal S` cancels in pairs
  have hzero : ∑ u ∈ T.erase (bal S), f.coeff u = 0 := by
    refine Finset.sum_involution (fun u _ => Finsupp.mapDomain Sum.swap u) ?_ ?_ ?_ ?_
    · intro u _
      rw [hcoeff]
      exact CharTwo.add_self_eq_zero _
    · intro u hu _ hcon
      exact Finset.ne_of_mem_erase hu (hfix u (Finset.mem_of_mem_erase hu) hcon)
    · intro u hu
      have hu' := Finset.mem_of_mem_erase hu
      refine Finset.mem_erase.mpr ⟨?_, hmemT u hu'⟩
      intro hcon
      refine Finset.ne_of_mem_erase hu ?_
      have h := congrArg (Finsupp.mapDomain (Sum.swap : ι ⊕ ι → ι ⊕ ι)) hcon
      rwa [mapDomain_swap_involutive, mapDomain_swap_bal] at h
    · intro u _
      exact mapDomain_swap_involutive u
  rw [hsum]
  by_cases hb : bal S ∈ T
  · rw [← Finset.sum_erase_add T _ hb, hzero, zero_add]
  · have h0 : f.coeff (bal S) = 0 := by
      by_contra hne
      exact hb (Finset.mem_filter.mpr
        ⟨MvPolynomial.mem_support_iff.mpr hne, mapDomain_elim_bal S⟩)
    rw [Finset.erase_eq_of_notMem hb] at hzero
    rw [hzero, h0]

/-- A multiple of the square of a variable has zero coefficient at a balanced (squarefree) monomial. -/
theorem coeff_bal_sq_mul (S : Finset ι) (v : ι ⊕ ι) (h : MvPolynomial (ι ⊕ ι) R) :
    (X v ^ 2 * h).coeff (bal S) = 0 := by
  classical
  rw [X_pow_eq_monomial, coeff_monomial_mul', if_neg]
  intro hle
  have h2 := Finsupp.le_def.mp hle v
  rw [Finsupp.single_eq_same] at h2
  have h3 := bal_apply_le_one S v
  omega

/-- Adding multiples of squares of variables does not change balanced coefficients of a product. -/
lemma coeff_bal_prod_add {κ : Type*} [DecidableEq κ] (S : Finset ι)
    (a s : κ → MvPolynomial (ι ⊕ ι) R)
    (hs : ∀ e, ∃ (v : ι ⊕ ι) (h : MvPolynomial (ι ⊕ ι) R), s e = X v ^ 2 * h)
    (T : Finset κ) (b : MvPolynomial (ι ⊕ ι) R) :
    (b * ∏ e ∈ T, (a e + s e)).coeff (bal S) = (b * ∏ e ∈ T, a e).coeff (bal S) := by
  induction T using Finset.induction_on generalizing b with
  | empty => simp
  | insert x T hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      obtain ⟨v, h, hv⟩ := hs x
      have key : b * ((a x + s x) * ∏ e ∈ T, (a e + s e))
          = (b * a x) * (∏ e ∈ T, (a e + s e))
            + X v ^ 2 * (b * h * ∏ e ∈ T, (a e + s e)) := by
        rw [hv]; ring
      rw [key, MvPolynomial.coeff_add, coeff_bal_sq_mul, add_zero, ih (b * a x), mul_assoc]

/-- **Key identity.** Let `g p q` be polynomials with `g p q (Y, X) = g p q (X, Y) + X_p²Y_q² + X_q²Y_p²`
and `g p q (X, X) = 0`. Then for every perfect matching `σ` of `ι`, the product of the `g` over the edges
of `σ` has coefficient `1` at the balanced monomial `∏_i X_i Y_i`. -/
theorem coeff_bal_prod_matching [CharP R 2] [LinearOrder ι]
    (g : ι → ι → MvPolynomial (ι ⊕ ι) R)
    (hswap : ∀ p q, p ≠ q → swapXY (g p q) = g p q + (X (Sum.inl p) * X (Sum.inr q)) ^ 2
      + (X (Sum.inl q) * X (Sum.inr p)) ^ 2)
    (hdiag : ∀ p q, p ≠ q → diagXY (g p q) = 0)
    (σ : Equiv.Perm ι) (hσ : σ ∈ PM ι) :
    (pfTerm (Matrix.of g) σ).coeff (bal (Finset.univ : Finset ι)) = 1 := by
  classical
  set E : Finset ι := Finset.univ.filter (fun i : ι => i < σ i) with hE
  set g' : ι → MvPolynomial (ι ⊕ ι) R :=
    fun i => g i (σ i) + (X (Sum.inl i) * X (Sum.inr (σ i))) ^ 2 with hg'
  have hne : ∀ i : ι, i ≠ σ i := fun i h => PM_apply_ne hσ i h.symm
  -- (iii) the extra squares do not change the balanced coefficient
  have key1 : (∏ i ∈ E, g' i).coeff (bal (Finset.univ : Finset ι))
      = (∏ i ∈ E, g i (σ i)).coeff (bal (Finset.univ : Finset ι)) := by
    have hs : ∀ e : ι, ∃ (v : ι ⊕ ι) (h : MvPolynomial (ι ⊕ ι) R),
        (X (Sum.inl e) * X (Sum.inr (σ e))) ^ 2 = X v ^ 2 * h :=
      fun e => ⟨Sum.inl e, X (Sum.inr (σ e)) ^ 2, by ring⟩
    have h := coeff_bal_prod_add (R := R) (Finset.univ : Finset ι)
      (fun i => g i (σ i)) (fun i => (X (Sum.inl i) * X (Sum.inr (σ i))) ^ 2) hs E 1
    simpa [hg'] using h
  -- (i) the perturbed product is swap-invariant
  have hsw : swapXY (∏ i ∈ E, g' i) = ∏ i ∈ E, g' i := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := hswap i (σ i) (hne i)
    have e1 : swapXY (g' i) = (g i (σ i) + (X (Sum.inl i) * X (Sum.inr (σ i))) ^ 2)
        + ((X (Sum.inl (σ i)) * X (Sum.inr i)) ^ 2
          + (X (Sum.inl (σ i)) * X (Sum.inr i)) ^ 2) := by
      rw [hg']
      simp only [map_add, map_pow, map_mul, swapXY_X, Sum.swap_inl, Sum.swap_inr, h]
      ring
    rw [e1, CharTwo.add_self_eq_zero, add_zero, hg']
  -- (ii) the diagonal substitution
  have hdg : diagXY (∏ i ∈ E, g' i) = ∏ i ∈ E, ((X i : MvPolynomial ι R) * X (σ i)) ^ 2 := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hg', map_add, hdiag i (σ i) (hne i), zero_add]
    simp
  -- (iv) the diagonal product is the square monomial
  have hprod : (∏ i ∈ E, ((X i : MvPolynomial ι R) * X (σ i)) ^ 2)
      = monomial (dbl (Finset.univ : Finset ι)) 1 := by
    rw [Finset.prod_pow, hE, PM_prod_edges hσ (fun i => (X i : MvPolynomial ι R)),
      ← Finset.prod_pow]
    exact prod_X_sq_eq_monomial_dbl _
  rw [pfTerm]
  simp only [Matrix.of_apply, ← hE]
  rw [← key1, coeff_bal_of_swap_invariant _ hsw, hdg, hprod, coeff_monomial, if_pos rfl]

/-- Lower-order perturbations do not change the top coefficient: if `G p q = g p q + c p q` with `g p q`
homogeneous of degree `4` and `c p q` of total degree `≤ 3`, the coefficient at the balanced monomial of
the matching product is unchanged. -/
theorem coeff_bal_pfTerm_perturb [LinearOrder ι]
    (g c : ι → ι → MvPolynomial (ι ⊕ ι) R)
    (hg : ∀ p q, (g p q).IsHomogeneous 4) (hc : ∀ p q, (c p q).totalDegree ≤ 3)
    (σ : Equiv.Perm ι) (hσ : σ ∈ PM ι) :
    (pfTerm (Matrix.of fun p q => g p q + c p q) σ).coeff (bal (Finset.univ : Finset ι))
      = (pfTerm (Matrix.of g) σ).coeff (bal (Finset.univ : Finset ι)) := by
  classical
  set a : ι → MvPolynomial (ι ⊕ ι) R := fun i => g i (σ i) with ha
  set d : ι → MvPolynomial (ι ⊕ ι) R := fun i => c i (σ i) with hd
  have ha4 : ∀ i, (a i).totalDegree ≤ 4 := fun i => (hg i (σ i)).totalDegree_le
  have hd3 : ∀ i, (d i).totalDegree ≤ 3 := fun i => hc i (σ i)
  have had4 : ∀ i, (a i + d i).totalDegree ≤ 4 := fun i =>
    (MvPolynomial.totalDegree_add _ _).trans (max_le (ha4 i) ((hd3 i).trans (by norm_num)))
  have hPle : ∀ T : Finset ι, (∏ i ∈ T, (a i + d i)).totalDegree ≤ 4 * T.card := by
    intro T
    refine (MvPolynomial.totalDegree_finsetProd T _).trans ?_
    calc ∑ i ∈ T, (a i + d i).totalDegree ≤ ∑ _i ∈ T, 4 :=
          Finset.sum_le_sum fun i _ => had4 i
      _ = 4 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hdiff : ∀ T : Finset ι, T.Nonempty →
      ((∏ i ∈ T, (a i + d i)) - ∏ i ∈ T, a i).totalDegree < 4 * T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro h; simp at h
    | insert x T hx ih =>
        intro _
        rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
        have key : (a x + d x) * (∏ i ∈ T, (a i + d i)) - a x * ∏ i ∈ T, a i
            = d x * (∏ i ∈ T, (a i + d i))
              + a x * ((∏ i ∈ T, (a i + d i)) - ∏ i ∈ T, a i) := by ring
        rw [key]
        refine lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _) ?_
        rw [max_lt_iff]
        refine ⟨?_, ?_⟩
        · refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
          have h1 := hPle T
          have h2 := hd3 x
          omega
        · rcases T.eq_empty_or_nonempty with rfl | hT
          · simp
          · refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
            have h1 := ih hT
            have h2 := ha4 x
            omega
  -- the degree of the balanced monomial
  have hsupp : (bal (Finset.univ : Finset ι)).support = (Finset.univ : Finset (ι ⊕ ι)) := by
    ext v
    simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true]
    cases v <;> simp
  have hbalsum : ∑ v ∈ (bal (Finset.univ : Finset ι)).support,
      (bal (Finset.univ : Finset ι)) v = 2 * Fintype.card ι := by
    rw [hsupp]
    have : ∀ v : ι ⊕ ι, (bal (Finset.univ : Finset ι)) v = 1 := by
      intro v; cases v <;> simp
    rw [Finset.sum_congr rfl fun v _ => this v]
    simp [Fintype.card_sum, two_mul]
  rw [pfTerm, pfTerm]
  simp only [Matrix.of_apply, ← ha]
  set E : Finset ι := Finset.univ.filter (fun i : ι => i < σ i) with hE
  rcases E.eq_empty_or_nonempty with hEe | hEn
  · rw [hEe]; simp
  · have hcard : 4 * E.card = 2 * Fintype.card ι := by
      have h := PM_card_edges hσ
      rw [← hE] at h
      omega
    have hz : ((∏ i ∈ E, (a i + d i)) - ∏ i ∈ E, a i).coeff
        (bal (Finset.univ : Finset ι)) = 0 := by
      refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
      rw [hbalsum, ← hcard]
      exact hdiff E hEn
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at hz
    exact hz

end AltCounter
