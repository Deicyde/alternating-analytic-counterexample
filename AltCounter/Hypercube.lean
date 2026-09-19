/-
Hypercube sums in characteristic 2: the sum of a polynomial of degree at most the number of variables over all
`0/1` points is the coefficient of the squarefree monomial `∏ X_i`.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

namespace AltCounter

open MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The `0/1` point attached to a subset `S` of the variables: `1` on `S`, `0` elsewhere. -/
def cubePt (S : Finset σ) : σ → R := fun i => if i ∈ S then 1 else 0

omit [Fintype σ] in
/-- A monomial takes the value of its coefficient at the `0/1` point of `S` when all of its
variables lie in `S`, and the value `0` otherwise. -/
lemma eval_cubePt_monomial (S : Finset σ) (u : σ →₀ ℕ) (c : R) :
    eval (cubePt S) (monomial u c) = if u.support ⊆ S then c else 0 := by
  rw [eval_monomial, Finsupp.prod]
  by_cases h : u.support ⊆ S
  · rw [ite_eq_left h, Finset.prod_eq_one, mul_one]
    intro i hi
    have hi1 : cubePt (R := R) S i = 1 := by simp [cubePt, h hi]
    rw [hi1, one_pow]
  · rw [ite_eq_right h]
    obtain ⟨j, hj, hjS⟩ := Finset.not_subset.mp h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hj ?_)
    have hj0 : cubePt (R := R) S j = 0 := by simp [cubePt, hjS]
    rw [hj0, zero_pow (Finsupp.mem_support_iff.mp hj)]

/-- The subsets of a finite type containing a fixed subset `T` are in bijection with the subsets of
the complement of `T`, so there are `2 ^ (card σ - card T)` of them. -/
lemma card_filter_superset (T : Finset σ) :
    (Finset.univ.filter fun S : Finset σ => T ⊆ S).card = 2 ^ (Fintype.card σ - T.card) := by
  have hb : (Finset.univ.filter fun S : Finset σ => T ⊆ S).card = (Tᶜ.powerset).card := by
    refine Finset.card_bij' (fun S _ => S \ T) (fun U _ => U ∪ T) ?_ ?_ ?_ ?_
    · intro S _
      refine Finset.mem_powerset.mpr fun x hx => ?_
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_compl.mpr hx.2
    · intro U _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_right⟩
    · intro S hS
      exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp hS).2
    · intro U hU
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint]
      exact Finset.disjoint_left.mpr fun a ha =>
        Finset.mem_compl.mp (Finset.mem_powerset.mp hU ha)
  rw [hb, Finset.card_powerset, Finset.card_compl]

omit [DecidableEq σ] in
/-- If every variable occurs in `u` and the total degree of `u` is at most the number of variables,
then every exponent of `u` is `1`. -/
lemma eq_of_support_eq_univ {u m : σ →₀ ℕ} (hm : ∀ i, m i = 1)
    (hsupp : u.support = Finset.univ) (hdeg : (u.sum fun _ e => e) ≤ Fintype.card σ) :
    u = m := by
  have h1 : ∀ i ∈ (Finset.univ : Finset σ), 1 ≤ u i := by
    intro i _
    refine Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ?_)
    rw [hsupp]
    exact Finset.mem_univ i
  have hsum : ∑ i : σ, u i ≤ Fintype.card σ := by
    rwa [Finsupp.sum, hsupp] at hdeg
  have heq : ∑ _i : σ, (1 : ℕ) = ∑ i : σ, u i :=
    le_antisymm (Finset.sum_le_sum h1) (by simpa using hsum)
  have hall := (Finset.sum_eq_sum_iff_of_le h1).mp heq
  exact Finsupp.ext fun i => ((hall i (Finset.mem_univ i)).symm).trans (hm i).symm

/-- **Hypercube sum.** Over a ring of characteristic 2, if `f` has total degree at most the number of variables and
`m` is the monomial in which every variable has exponent `1`, then the sum of the values of `f` over all `0/1` points
is the coefficient of `m` in `f`. (A monomial which misses a variable is `1` at an even number of `0/1` points.) -/
theorem sum_eval_cubePt [CharP R 2] (f : MvPolynomial σ R) (m : σ →₀ ℕ) (hm : ∀ i, m i = 1)
    (hf : f.totalDegree ≤ Fintype.card σ) :
    ∑ S : Finset σ, eval (cubePt S) f = f.coeff m := by
  -- The indicator of the supersets of `T` sums to the number of such supersets.
  have hcount : ∀ (T : Finset σ) (c : R),
      ∑ S : Finset σ, (if T ⊆ S then c else 0)
        = ((2 ^ (Fintype.card σ - T.card) : ℕ) : R) * c := by
    intro T c
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      card_filter_superset, nsmul_eq_mul]
  -- Only the squarefree monomial `m` survives: every other monomial misses a variable, hence is
  -- `1` at an even number of points.
  have key : ∀ u ∈ f.support,
      ∑ S : Finset σ, (if u.support ⊆ S then f.coeff u else 0)
        = if u = m then f.coeff m else 0 := by
    intro u hu
    rw [hcount]
    by_cases hsupp : u.support = Finset.univ
    · have hum : u = m := eq_of_support_eq_univ hm hsupp (le_trans (le_totalDegree hu) hf)
      rw [hsupp, Finset.card_univ, Nat.sub_self, pow_zero, Nat.cast_one, one_mul,
        ite_eq_left hum, hum]
    · have hlt : u.support.card < Fintype.card σ := by
        rw [← Finset.card_univ]
        exact Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ _) hsupp)
      have hpos : 0 < Fintype.card σ - u.support.card := Nat.sub_pos_of_lt hlt
      have hz : ((2 ^ (Fintype.card σ - u.support.card) : ℕ) : R) = 0 := by
        push_cast
        rw [CharTwo.two_eq_zero, zero_pow hpos.ne']
      rw [hz, zero_mul, ite_eq_right]
      rintro rfl
      exact hsupp (by ext i; simp [Finsupp.mem_support_iff, hm i])
  calc ∑ S : Finset σ, eval (cubePt S) f
      = ∑ S : Finset σ, ∑ u ∈ f.support, eval (cubePt S) (monomial u (f.coeff u)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        conv_lhs => rw [f.as_sum]
        rw [map_sum]
    _ = ∑ S : Finset σ, ∑ u ∈ f.support, (if u.support ⊆ S then f.coeff u else 0) :=
        Finset.sum_congr rfl fun S _ =>
          Finset.sum_congr rfl fun u _ => eval_cubePt_monomial S u (f.coeff u)
    _ = ∑ u ∈ f.support, ∑ S : Finset σ, (if u.support ⊆ S then f.coeff u else 0) :=
        Finset.sum_comm
    _ = ∑ u ∈ f.support, if u = m then f.coeff m else 0 := Finset.sum_congr rfl key
    _ = f.coeff m := by
        rw [Finset.sum_ite_eq' f.support m fun _ => f.coeff m]
        by_cases h : m ∈ f.support
        · rw [ite_eq_left h]
        · rw [ite_eq_right h, (notMem_support_iff.mp h)]

end AltCounter
