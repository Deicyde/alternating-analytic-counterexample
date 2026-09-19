/-
The finite identity: for every "lift" on a block of even size there is a `0/1` point at which the block matrix has
determinant of norm `≥ 1`.
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import AltCounter.Defs
import AltCounter.Balanced
import AltCounter.Hypercube

namespace AltCounter

open BoundedContinuousFunction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The sequence supported on the block `[s, s + n)` with entries `x`. -/
noncomputable def blockVec {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) : Linf 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => if h : s ≤ k ∧ k < s + n then x ⟨k - s, by omega⟩ else 0) (∑ i, ‖x i‖) (by
      intro k
      split_ifs with h
      · exact Finset.single_le_sum (f := fun i => ‖x i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ _)
      · simpa using Finset.sum_nonneg (fun i _ => norm_nonneg (x i)))

theorem blockVec_apply_def {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (k : ℕ) :
    blockVec s x k = if h : s ≤ k ∧ k < s + n then x ⟨k - s, by omega⟩ else 0 := rfl

theorem blockVec_apply_block {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (i : Fin n) :
    blockVec s x (s + i) = x i := by
  rw [blockVec_apply_def, dif_pos ⟨Nat.le_add_right _ _, by omega⟩]
  congr 1
  exact Fin.ext (by simp)

theorem blockVec_apply_of_lt {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (k : ℕ) (hk : k < s) :
    blockVec s x k = 0 := by
  rw [blockVec_apply_def, dif_neg (by omega)]

theorem blockVec_apply_of_ge {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (k : ℕ) (hk : s + n ≤ k) :
    blockVec s x k = 0 := by
  rw [blockVec_apply_def, dif_neg (by omega)]

theorem norm_blockVec_apply_le {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (hx : ∀ i, ‖x i‖ ≤ 1) (k : ℕ) :
    ‖blockVec s x k‖ ≤ 1 := by
  rw [blockVec_apply_def]
  split_ifs with h
  · exact hx _
  · simpa using zero_le_one

theorem norm_blockVec_le {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖blockVec s x‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2 (norm_blockVec_apply_le s x hx)

/-- If `a'` vanishes from `s` on and `‖a'‖ ≤ 1`, `‖x i‖ ≤ 1`, then `‖a' + blockVec s x‖ ≤ 1`. -/
theorem norm_add_blockVec_le {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (hx : ∀ i, ‖x i‖ ≤ 1) (a' : Linf 𝕜)
    (ha' : ∀ k, s ≤ k → a' k = 0) (hn : ‖a'‖ ≤ 1) : ‖a' + blockVec s x‖ ≤ 1 := by
  refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun k => ?_
  rw [BoundedContinuousFunction.add_apply]
  rcases lt_or_ge k s with hk | hk
  · rw [blockVec_apply_of_lt s x k hk, add_zero]
    exact le_trans (BoundedContinuousFunction.norm_coe_le_norm a' k) hn
  · rw [ha' k hk, zero_add]
    exact norm_blockVec_apply_le s x hx k

/-- `blockVec` is the linear combination of the block basis vectors. -/
theorem blockVec_eq_sum {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) :
    blockVec s x = ∑ i, x i • blockVec s (Pi.single i (1 : 𝕜)) := by
  ext k
  rw [BoundedContinuousFunction.sum_apply]
  rcases lt_or_ge k s with hk | hk
  · rw [blockVec_apply_of_lt s x k hk]
    simp [BoundedContinuousFunction.smul_apply, blockVec_apply_of_lt s _ k hk]
  rcases lt_or_ge k (s + n) with hk2 | hk2
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n, k = s + (j : ℕ) := ⟨⟨k - s, by omega⟩, by simp; omega⟩
    rw [blockVec_apply_block]
    simp only [BoundedContinuousFunction.smul_apply, blockVec_apply_block, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) j x]
    simp
  · rw [blockVec_apply_of_ge s x k hk2]
    simp [BoundedContinuousFunction.smul_apply, blockVec_apply_of_ge s _ k hk2]

/-! ### Multilinear expansion of a bounded 4-linear form -/

namespace IsBdd4

variable {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜} {C₀ : ℝ}

theorem zero₁ (h : IsBdd4 𝕜 Λ C₀) (b x y : Linf 𝕜) : Λ 0 b x y = 0 := by
  simpa using h.smul₁ 0 0 b x y

theorem zero₂ (h : IsBdd4 𝕜 Λ C₀) (a x y : Linf 𝕜) : Λ a 0 x y = 0 := by
  simpa using h.smul₂ 0 a 0 x y

theorem zero₃ (h : IsBdd4 𝕜 Λ C₀) (a b y : Linf 𝕜) : Λ a b 0 y = 0 := by
  simpa using h.smul₃ 0 a b 0 y

theorem zero₄ (h : IsBdd4 𝕜 Λ C₀) (a b x : Linf 𝕜) : Λ a b x 0 = 0 := by
  simpa using h.smul₄ 0 a b x 0

variable {κ : Type*}

theorem sum₁ (h : IsBdd4 𝕜 Λ C₀) (t : Finset κ) (c : κ → 𝕜) (v : κ → Linf 𝕜) (b x y : Linf 𝕜) :
    Λ (∑ k ∈ t, c k • v k) b x y = ∑ k ∈ t, c k * Λ (v k) b x y := by
  classical
  induction t using Finset.induction with
  | empty => simpa using h.zero₁ b x y
  | insert a t ha ih => rw [Finset.sum_insert ha, h.add₁, h.smul₁, ih, Finset.sum_insert ha]

theorem sum₂ (h : IsBdd4 𝕜 Λ C₀) (t : Finset κ) (c : κ → 𝕜) (v : κ → Linf 𝕜) (a x y : Linf 𝕜) :
    Λ a (∑ k ∈ t, c k • v k) x y = ∑ k ∈ t, c k * Λ a (v k) x y := by
  classical
  induction t using Finset.induction with
  | empty => simpa using h.zero₂ a x y
  | insert a t ha ih => rw [Finset.sum_insert ha, h.add₂, h.smul₂, ih, Finset.sum_insert ha]

theorem sum₃ (h : IsBdd4 𝕜 Λ C₀) (t : Finset κ) (c : κ → 𝕜) (v : κ → Linf 𝕜) (a b y : Linf 𝕜) :
    Λ a b (∑ k ∈ t, c k • v k) y = ∑ k ∈ t, c k * Λ a b (v k) y := by
  classical
  induction t using Finset.induction with
  | empty => simpa using h.zero₃ a b y
  | insert a t ha ih => rw [Finset.sum_insert ha, h.add₃, h.smul₃, ih, Finset.sum_insert ha]

theorem sum₄ (h : IsBdd4 𝕜 Λ C₀) (t : Finset κ) (c : κ → 𝕜) (v : κ → Linf 𝕜) (a b x : Linf 𝕜) :
    Λ a b x (∑ k ∈ t, c k • v k) = ∑ k ∈ t, c k * Λ a b x (v k) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using h.zero₄ a b x
  | insert a t ha ih => rw [Finset.sum_insert ha, h.add₄, h.smul₄, ih, Finset.sum_insert ha]

/-- Full 4-fold expansion. -/
theorem sum4 (h : IsBdd4 𝕜 Λ C₀) [Fintype κ] (ca cb : κ → 𝕜) (va vb : κ → Linf 𝕜) :
    Λ (∑ k, ca k • va k) (∑ k, cb k • vb k) (∑ k, ca k • va k) (∑ k, cb k • vb k)
      = ∑ k1, ca k1 * ∑ k2, cb k2 * ∑ k3, ca k3 * ∑ k4, cb k4 *
          Λ (va k1) (vb k2) (va k3) (vb k4) := by
  rw [h.sum₁]
  refine Finset.sum_congr rfl fun k1 _ => ?_
  congr 1
  rw [h.sum₂]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  congr 1
  rw [h.sum₃]
  refine Finset.sum_congr rfl fun k3 _ => ?_
  congr 1
  rw [h.sum₄]

end IsBdd4

/-! ### The polynomial attached to a block -/

open MvPolynomial

/-- `X_{e i}` for `some i`, the constant `c` for `none`. -/
noncomputable def monoC {n : ℕ} (e : Fin n → Fin n ⊕ Fin n) (c : 𝕜) :
    Option (Fin n) → MvPolynomial (Fin n ⊕ Fin n) 𝕜
  | none => C c
  | some i => X (e i)

@[simp] theorem monoC_none {n : ℕ} (e : Fin n → Fin n ⊕ Fin n) (c : 𝕜) :
    monoC e c none = C c := rfl

@[simp] theorem monoC_some {n : ℕ} (e : Fin n → Fin n ⊕ Fin n) (c : 𝕜) (i : Fin n) :
    monoC e c (some i) = X (e i) := rfl

/-- `c` for `none`, `x i` for `some i`. -/
def coefOpt {n : ℕ} (c : 𝕜) (x : Fin n → 𝕜) : Option (Fin n) → 𝕜
  | none => c
  | some i => x i

@[simp] theorem coefOpt_none {n : ℕ} (c : 𝕜) (x : Fin n → 𝕜) : coefOpt c x none = c := rfl

@[simp] theorem coefOpt_some {n : ℕ} (c : 𝕜) (x : Fin n → 𝕜) (i : Fin n) :
    coefOpt c x (some i) = x i := rfl

/-- `a` for `none`, the `i`-th basis vector of the block for `some i`. -/
noncomputable def vecOpt {n : ℕ} (s : ℕ) (a : Linf 𝕜) : Option (Fin n) → Linf 𝕜
  | none => a
  | some i => blockVec s (Pi.single i (1 : 𝕜))

@[simp] theorem vecOpt_none {n : ℕ} (s : ℕ) (a : Linf 𝕜) :
    (vecOpt s a : Option (Fin n) → Linf 𝕜) none = a := rfl

@[simp] theorem vecOpt_some {n : ℕ} (s : ℕ) (a : Linf 𝕜) (i : Fin n) :
    vecOpt s a (some i) = blockVec s (Pi.single i (1 : 𝕜)) := rfl

theorem sum_coefOpt_smul_vecOpt {n : ℕ} (s : ℕ) (a : Linf 𝕜) (c : 𝕜) (x : Fin n → 𝕜) :
    ∑ k : Option (Fin n), coefOpt c x k • vecOpt s a k = c • a + blockVec s x := by
  rw [Fintype.sum_option]
  simp only [coefOpt_none, coefOpt_some, vecOpt_none, vecOpt_some]
  rw [← blockVec_eq_sum]

/-- The polynomial in `2n` variables whose value at `(x, y)` is
`Λ (c • a + blockVec s x) (c • b + blockVec s y) (c • a + blockVec s x) (c • b + blockVec s y)`. -/
noncomputable def Gpoly (Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (s : ℕ) (a b : Linf 𝕜)
    (c : 𝕜) (n : ℕ) : MvPolynomial (Fin n ⊕ Fin n) 𝕜 :=
  ∑ k1 : Option (Fin n), ∑ k2 : Option (Fin n), ∑ k3 : Option (Fin n), ∑ k4 : Option (Fin n),
    monoC Sum.inl c k1 * monoC Sum.inr c k2 * monoC Sum.inl c k3 * monoC Sum.inr c k4 *
      C (Λ (vecOpt s a k1) (vecOpt s b k2) (vecOpt s a k3) (vecOpt s b k4))

theorem eval_monoC_inl {n : ℕ} (c : 𝕜) (x y : Fin n → 𝕜) (k : Option (Fin n)) :
    eval (Sum.elim x y) (monoC Sum.inl c k) = coefOpt c x k := by
  cases k <;> simp

theorem eval_monoC_inr {n : ℕ} (c : 𝕜) (x y : Fin n → 𝕜) (k : Option (Fin n)) :
    eval (Sum.elim x y) (monoC Sum.inr c k) = coefOpt c y k := by
  cases k <;> simp

theorem eval_Gpoly {n : ℕ} {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜} {C₀ : ℝ}
    (hL : IsBdd4 𝕜 Λ C₀) (s : ℕ) (a b : Linf 𝕜) (c : 𝕜) (x y : Fin n → 𝕜) :
    eval (Sum.elim x y) (Gpoly Λ s a b c n)
      = Λ (c • a + blockVec s x) (c • b + blockVec s y) (c • a + blockVec s x)
          (c • b + blockVec s y) := by
  rw [← sum_coefOpt_smul_vecOpt s a c x, ← sum_coefOpt_smul_vecOpt s b c y, hL.sum4]
  simp only [Gpoly, map_sum, map_mul, eval_C, eval_monoC_inl, eval_monoC_inr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ =>
    Finset.sum_congr rfl fun k3 _ => Finset.sum_congr rfl fun k4 _ => by ring

theorem monoC_zero_isHomogeneous {n : ℕ} (e : Fin n → Fin n ⊕ Fin n) (k : Option (Fin n)) :
    (monoC e (0 : 𝕜) k).IsHomogeneous 1 := by
  cases k with
  | none => rw [monoC_none, map_zero]; exact isHomogeneous_zero ..
  | some i => rw [monoC_some]; exact isHomogeneous_X ..

theorem Gpoly_zero_isHomogeneous {n : ℕ} (Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (s : ℕ)
    (a b : Linf 𝕜) : (Gpoly Λ s a b (0 : 𝕜) n).IsHomogeneous 4 := by
  simp only [Gpoly]
  refine IsHomogeneous.sum _ _ _ fun k1 _ => IsHomogeneous.sum _ _ _ fun k2 _ =>
    IsHomogeneous.sum _ _ _ fun k3 _ => IsHomogeneous.sum _ _ _ fun k4 _ => ?_
  have h := ((((monoC_zero_isHomogeneous Sum.inl k1).mul
      (monoC_zero_isHomogeneous Sum.inr k2)).mul
      (monoC_zero_isHomogeneous Sum.inl k3)).mul
      (monoC_zero_isHomogeneous Sum.inr k4)).mul
      (isHomogeneous_C (σ := Fin n ⊕ Fin n) (R := 𝕜)
        (Λ (vecOpt s a k1) (vecOpt s b k2) (vecOpt s a k3) (vecOpt s b k4)))
  simpa using h

theorem totalDegree_mul4C {σ : Type*} (u1 u2 u3 u4 : MvPolynomial σ 𝕜) (v : 𝕜)
    (d1 d2 d3 d4 d : ℕ) (h1 : u1.totalDegree ≤ d1) (h2 : u2.totalDegree ≤ d2)
    (h3 : u3.totalDegree ≤ d3) (h4 : u4.totalDegree ≤ d4) (hd : d1 + d2 + d3 + d4 ≤ d) :
    (u1 * u2 * u3 * u4 * C v).totalDegree ≤ d := by
  refine le_trans ?_ hd
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, add_zero]
  refine le_trans (totalDegree_mul _ _) (add_le_add ?_ h4)
  refine le_trans (totalDegree_mul _ _) (add_le_add ?_ h3)
  exact le_trans (totalDegree_mul _ _) (add_le_add h1 h2)

theorem monoC_totalDegree_le {n : ℕ} (e : Fin n → Fin n ⊕ Fin n) (c : 𝕜) (k : Option (Fin n)) :
    (monoC e c k).totalDegree ≤ 1 := by
  cases k with
  | none => simp
  | some i => simp

theorem totalDegree_Gpoly_sub {n : ℕ} (Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (s : ℕ)
    (a b : Linf 𝕜) :
    (Gpoly Λ s a b (1 : 𝕜) n - Gpoly Λ s a b (0 : 𝕜) n).totalDegree ≤ 3 := by
  have key : ∀ k1 k2 k3 k4 : Option (Fin n),
      (monoC Sum.inl (1 : 𝕜) k1 * monoC Sum.inr (1 : 𝕜) k2 * monoC Sum.inl (1 : 𝕜) k3 *
          monoC Sum.inr (1 : 𝕜) k4 *
          C (Λ (vecOpt s a k1) (vecOpt s b k2) (vecOpt s a k3) (vecOpt s b k4))
        - monoC Sum.inl (0 : 𝕜) k1 * monoC Sum.inr (0 : 𝕜) k2 * monoC Sum.inl (0 : 𝕜) k3 *
          monoC Sum.inr (0 : 𝕜) k4 *
          C (Λ (vecOpt s a k1) (vecOpt s b k2) (vecOpt s a k3) (vecOpt s b k4))).totalDegree
        ≤ 3 := by
    intro k1 k2 k3 k4
    have hz : ∀ (e : Fin n → Fin n ⊕ Fin n),
        (monoC e (0 : 𝕜) none : MvPolynomial (Fin n ⊕ Fin n) 𝕜) = 0 := by
      intro e; rw [monoC_none, map_zero]
    have hC1 : ∀ (e : Fin n → Fin n ⊕ Fin n),
        (monoC e (1 : 𝕜) none : MvPolynomial (Fin n ⊕ Fin n) 𝕜).totalDegree ≤ 0 := by
      intro e; rw [monoC_none, totalDegree_C]
    rcases k1 with _ | i1
    · rw [hz Sum.inl]
      simp only [zero_mul, sub_zero]
      exact totalDegree_mul4C _ _ _ _ _ 0 1 1 1 3 (hC1 Sum.inl) (monoC_totalDegree_le _ _ _)
        (monoC_totalDegree_le _ _ _) (monoC_totalDegree_le _ _ _) (by norm_num)
    rcases k2 with _ | i2
    · rw [hz Sum.inr]
      simp only [mul_zero, zero_mul, sub_zero]
      exact totalDegree_mul4C _ _ _ _ _ 1 0 1 1 3 (monoC_totalDegree_le _ _ _) (hC1 Sum.inr)
        (monoC_totalDegree_le _ _ _) (monoC_totalDegree_le _ _ _) (by norm_num)
    rcases k3 with _ | i3
    · rw [hz Sum.inl]
      simp only [mul_zero, zero_mul, sub_zero]
      exact totalDegree_mul4C _ _ _ _ _ 1 1 0 1 3 (monoC_totalDegree_le _ _ _)
        (monoC_totalDegree_le _ _ _) (hC1 Sum.inl) (monoC_totalDegree_le _ _ _) (by norm_num)
    rcases k4 with _ | i4
    · rw [hz Sum.inr]
      simp only [mul_zero, zero_mul, sub_zero]
      exact totalDegree_mul4C _ _ _ _ _ 1 1 1 0 3 (monoC_totalDegree_le _ _ _)
        (monoC_totalDegree_le _ _ _) (monoC_totalDegree_le _ _ _) (hC1 Sum.inr) (by norm_num)
    · simp
  simp only [Gpoly, ← Finset.sum_sub_distrib]
  exact totalDegree_finsetSum_le fun k1 _ => totalDegree_finsetSum_le fun k2 _ =>
    totalDegree_finsetSum_le fun k3 _ => totalDegree_finsetSum_le fun k4 _ => key k1 k2 k3 k4

/-! ### Characteristic-two algebra -/

theorem eq_of_add_eq_zero_two {R : Type*} [CommRing R] [CharP R 2] {a b : R} (h : a + b = 0) :
    a = b := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination h - b * h2

/-- The algebraic core of the swap identity. -/
theorem char2_key {R : Type*} [CommRing R] [CharP R 2] (α β γ ζ ε δ xp xq yp yq : R)
    (e1 : ε = α + β + γ + ζ)
    (e2 : ε = (xp + yp) * xp * ((xq + yq) * yq) + (xp + yp) * yp * ((xq + yq) * xq))
    (e3 : α = xp * xp * (xq * yq) + xp * yp * (xq * xq))
    (e4 : ζ = yp * xp * (yq * yq) + yp * yp * (yq * xq))
    (e5 : γ = δ) :
    δ = β + (xp * yq) ^ 2 + (xq * yp) ^ 2 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination -e5 - e1 + e2 - e3 - e4 + (xp * yp * xq * yq - β) * h2

/-- In characteristic 2, a form vanishing on the diagonal of its last two slots is symmetric there. -/
theorem alt_symm [CharP 𝕜 2] {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜} {C₀ : ℝ}
    (hL : IsBdd4 𝕜 Λ C₀) (halt : ∀ a b u, Λ a b u u = 0) (a b u v : Linf 𝕜) :
    Λ a b u v = Λ a b v u := by
  have h := halt a b (u + v)
  rw [hL.add₃, hL.add₄, hL.add₄, halt, halt, zero_add, add_zero] at h
  exact eq_of_add_eq_zero_two h

/-! ### The two identities satisfied by the top part -/

theorem swapXY_Gpoly_zero [CharP 𝕜 2] {n : ℕ} {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜}
    {C₀ : ℝ} (hL : IsBdd4 𝕜 Λ C₀) (halt : ∀ a b u, Λ a b u u = 0) (s : ℕ) (a b : Linf 𝕜)
    (p q : Fin n)
    (hd : ∀ c u v : Linf 𝕜, Λ c c u v =
      c (s + (p : ℕ)) * u (s + (p : ℕ)) * (c (s + (q : ℕ)) * v (s + (q : ℕ)))
        + c (s + (p : ℕ)) * v (s + (p : ℕ)) * (c (s + (q : ℕ)) * u (s + (q : ℕ)))) :
    swapXY (Gpoly Λ s a b (0 : 𝕜) n)
      = Gpoly Λ s a b (0 : 𝕜) n + (X (Sum.inl p) * X (Sum.inr q)) ^ 2
        + (X (Sum.inl q) * X (Sum.inr p)) ^ 2 := by
  refine MvPolynomial.funext fun z => ?_
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin n → 𝕜, z = Sum.elim x y :=
    ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), by funext w; cases w <;> rfl⟩
  have hcomp : (Sum.elim x y) ∘ Sum.swap = Sum.elim y x := by funext w; cases w <;> rfl
  have hlhs : eval (Sum.elim x y) (swapXY (Gpoly Λ s a b (0 : 𝕜) n))
      = Λ (blockVec s y) (blockVec s x) (blockVec s y) (blockVec s x) := by
    show eval (Sum.elim x y) (rename Sum.swap (Gpoly Λ s a b (0 : 𝕜) n)) = _
    rw [eval_rename, hcomp, eval_Gpoly hL]
    simp
  rw [hlhs]
  simp only [map_add, map_pow, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr, eval_Gpoly hL,
    zero_smul, zero_add]
  set A := blockVec s x with hA
  set B := blockVec s y with hB
  have e1 : Λ (A + B) (A + B) A B = Λ A A A B + Λ A B A B + Λ B A A B + Λ B B A B := by
    rw [hL.add₁, hL.add₂, hL.add₂]; ring
  have e2 : Λ (A + B) (A + B) A B
      = (x p + y p) * x p * ((x q + y q) * y q) + (x p + y p) * y p * ((x q + y q) * x q) := by
    rw [hd]
    simp only [BoundedContinuousFunction.add_apply, hA, hB, blockVec_apply_block]
  have e3 : Λ A A A B = x p * x p * (x q * y q) + x p * y p * (x q * x q) := by
    rw [hd]
    simp only [hA, hB, blockVec_apply_block]
  have e4 : Λ B B A B = y p * x p * (y q * y q) + y p * y p * (y q * x q) := by
    rw [hd]
    simp only [hA, hB, blockVec_apply_block]
  have e5 : Λ B A A B = Λ B A B A := alt_symm hL halt _ _ _ _
  exact char2_key _ _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5

theorem diagXY_Gpoly_zero {n : ℕ} {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜} {C₀ : ℝ}
    (hL : IsBdd4 𝕜 Λ C₀) (halt : ∀ a b u, Λ a b u u = 0) (s : ℕ) (a b : Linf 𝕜) :
    diagXY (Gpoly Λ s a b (0 : 𝕜) n) = 0 := by
  refine MvPolynomial.funext fun z => ?_
  have hcomp : z ∘ (Sum.elim id id) = Sum.elim z z := by funext w; cases w <;> rfl
  show eval z (rename (Sum.elim id id) (Gpoly Λ s a b (0 : 𝕜) n)) = eval z 0
  rw [eval_rename, hcomp, eval_Gpoly hL]
  simp [halt]

/-- The family of polynomials indexed by the block. -/
noncomputable def blockFam (Λ : ℕ → ℕ → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (s : ℕ)
    (a b : Linf 𝕜) (c : 𝕜) (n : ℕ) : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) 𝕜 :=
  fun p q => Gpoly (Λ (s + (p : ℕ)) (s + (q : ℕ))) s a b c n

@[simp] theorem blockFam_apply (Λ : ℕ → ℕ → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (s : ℕ)
    (a b : Linf 𝕜) (c : 𝕜) {n : ℕ} (p q : Fin n) :
    blockFam Λ s a b c n p q = Gpoly (Λ (s + (p : ℕ)) (s + (q : ℕ))) s a b c n := rfl

variable [IsUltrametricDist 𝕜]

/-! ### From the hypercube sum to a `0/1` point of large determinant -/

/-- A matching product of entries of total degree at most `4` has total degree at most the number of
variables: the matching has `card ι / 2` edges, so the product has degree at most `2 * card ι`. -/
theorem totalDegree_pfTerm_le {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (G : ι → ι → MvPolynomial (ι ⊕ ι) R) (hG : ∀ p q, (G p q).totalDegree ≤ 4)
    {σ : Equiv.Perm ι} (hσ : σ ∈ PM ι) :
    (pfTerm (Matrix.of G) σ).totalDegree ≤ Fintype.card (ι ⊕ ι) := by
  classical
  rw [pfTerm]
  simp only [Matrix.of_apply]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have hcard := PM_card_edges hσ
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : ι => i < σ i), (G i (σ i)).totalDegree
      ≤ ∑ _i ∈ Finset.univ.filter (fun i : ι => i < σ i), 4 :=
    Finset.sum_le_sum fun i _ => hG i (σ i)
  rw [Finset.sum_const, smul_eq_mul] at h1
  rw [Fintype.card_sum]
  omega

/-- **Hypercube point.** Let `G` be a symmetric matrix with zero diagonal whose entries are
polynomials of total degree at most `4` in the `2 * card ι` variables `ι ⊕ ι`, over an ultrametric
field of characteristic `2`. If every matching term `pfTerm G σ` has coefficient `1` at the balanced
squarefree monomial `∏_i X_i Y_i`, and `card ι` is even, then `det G` has norm at least `1` at some
`0/1` point.

Indeed `det G = ∑_σ (pfTerm G σ)²`, each `pfTerm G σ` has total degree at most the number of
variables, so its values over the `0/1` points sum to its balanced coefficient, namely `1`; since
squaring is additive in characteristic `2`, the values of `det G` over the `0/1` points sum to the
number of perfect matchings, which is odd, hence to `1`. The ultrametric inequality then produces a
single `0/1` point where the determinant has norm at least `‖1‖ = 1`. -/
theorem exists_cubePt_norm_det_ge_one {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CharP 𝕜 2] (G : ι → ι → MvPolynomial (ι ⊕ ι) 𝕜)
    (hsymm : ∀ p q, G p q = G q p) (hdiag : ∀ p, G p p = 0)
    (hdeg : ∀ p q, (G p q).totalDegree ≤ 4)
    (hcoeff : ∀ σ ∈ PM ι, (pfTerm (Matrix.of G) σ).coeff (bal (Finset.univ : Finset ι)) = 1)
    (heven : Even (Fintype.card ι)) :
    ∃ z : ι ⊕ ι → 𝕜, (∀ i, ‖z i‖ ≤ 1) ∧ 1 ≤ ‖eval z (Matrix.of G).det‖ := by
  classical
  have hdet : (Matrix.of G).det = ∑ σ ∈ PM ι, (pfTerm (Matrix.of G) σ) ^ 2 :=
    det_eq_sum_PM_sq _ hsymm hdiag
  have hbal : ∀ v : ι ⊕ ι, (bal (Finset.univ : Finset ι)) v = 1 := by
    intro v; cases v <;> simp
  -- each matching term sums to its balanced coefficient, namely `1`, over the `0/1` points
  have hterm : ∀ σ ∈ PM ι,
      ∑ S : Finset (ι ⊕ ι), eval (cubePt S) (pfTerm (Matrix.of G) σ) = 1 := by
    intro σ hσ
    rw [sum_eval_cubePt _ _ hbal (totalDegree_pfTerm_le G hdeg hσ)]
    exact hcoeff σ hσ
  -- hence the determinant sums to the (odd) number of perfect matchings
  have hsum : ∑ S : Finset (ι ⊕ ι), eval (cubePt S) (Matrix.of G).det = 1 := by
    have h1 : ∀ S : Finset (ι ⊕ ι), eval (cubePt S) (Matrix.of G).det
        = ∑ σ ∈ PM ι, (eval (cubePt S) (pfTerm (Matrix.of G) σ)) ^ 2 := fun S => by
      rw [hdet, map_sum]
      exact Finset.sum_congr rfl fun σ _ => map_pow _ _ _
    have h2 : ∀ σ ∈ PM ι,
        ∑ S : Finset (ι ⊕ ι), (eval (cubePt S) (pfTerm (Matrix.of G) σ)) ^ 2 = 1 := by
      intro σ hσ
      rw [← sum_pow_char 2, hterm σ hσ, one_pow]
    rw [Finset.sum_congr rfl fun S _ => h1 S, Finset.sum_comm, Finset.sum_congr rfl h2,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := card_PM_odd (α := ι) heven
    rw [hk]
    push_cast
    simp [CharTwo.two_eq_zero]
  -- the ultrametric inequality picks out one of the `0/1` points
  obtain ⟨S, -, hS⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Finset (ι ⊕ ι)))
    (fun S : Finset (ι ⊕ ι) => eval (cubePt S) (Matrix.of G).det)
  refine ⟨cubePt S, fun i => ?_, ?_⟩
  · simp only [cubePt]
    split_ifs <;> simp
  · calc (1 : ℝ) = ‖(1 : 𝕜)‖ := norm_one.symm
      _ = ‖∑ T : Finset (ι ⊕ ι), eval (cubePt T) (Matrix.of G).det‖ := by rw [hsum]
      _ ≤ ‖eval (cubePt S) (Matrix.of G).det‖ := hS

/-- **Finite lemma.** For a family `Λ p q` of bounded 4-linear forms on `ℓ^∞` which is alternating in the last
two slots, symmetric with zero diagonal in `(p, q)`, and restricts on the diagonal `a = b` to
`W(a x, a y)_{pq}`, every block of even size `n` carries `0/1` valued vectors `x, y` — found by summing
the block determinant over the vertices of the hypercube — for which the `n × n` block of
`Λ (a' + x) (b' + y) (a' + x) (b' + y)` has determinant of norm at least `1`. -/
theorem exists_block_point [CharP 𝕜 2]
    (Λ : ℕ → ℕ → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (C : ℝ)
    (hlin : ∀ p q, IsBdd4 𝕜 (Λ p q) C)
    (halt : ∀ p q a b x, Λ p q a b x x = 0)
    (hdiag : ∀ p q a x y, Λ p q a a x y = a p * x p * (a q * y q) + a p * y p * (a q * x q))
    (hsymm : ∀ p q a b x y, Λ p q a b x y = Λ q p a b x y)
    (hzero : ∀ p a b x y, Λ p p a b x y = 0)
    (n : ℕ) (hn : Even n) (s : ℕ) (a' b' : Linf 𝕜) :
    ∃ x y : Fin n → 𝕜, (∀ i, ‖x i‖ ≤ 1) ∧ (∀ i, ‖y i‖ ≤ 1) ∧
      1 ≤ ‖(Matrix.of fun p q : Fin n =>
        Λ (s + p) (s + q) (a' + blockVec s x) (b' + blockVec s y)
          (a' + blockVec s x) (b' + blockVec s y)).det‖ := by
  classical
  have hGsymm : ∀ p q : Fin n, blockFam Λ s a' b' 1 n p q = blockFam Λ s a' b' 1 n q p := by
    intro p q
    have h : Λ (s + (p : ℕ)) (s + (q : ℕ)) = Λ (s + (q : ℕ)) (s + (p : ℕ)) := by
      funext u v w t; exact hsymm _ _ _ _ _ _
    simp only [blockFam_apply, h]
  have hGdiag : ∀ p : Fin n, blockFam Λ s a' b' 1 n p p = 0 := by
    intro p
    have h : Λ (s + (p : ℕ)) (s + (p : ℕ)) = fun _ _ _ _ => (0 : 𝕜) := by
      funext u v w t; exact hzero _ _ _ _ _
    simp only [blockFam_apply, h, Gpoly, map_zero, mul_zero, Finset.sum_const_zero]
  have hghom : ∀ p q : Fin n, (blockFam Λ s a' b' 0 n p q).IsHomogeneous 4 := fun p q =>
    Gpoly_zero_isHomogeneous _ _ _ _
  have hcdeg : ∀ p q : Fin n,
      (blockFam Λ s a' b' 1 n p q - blockFam Λ s a' b' 0 n p q).totalDegree ≤ 3 := fun p q =>
    totalDegree_Gpoly_sub _ _ _ _
  have hgswap : ∀ p q : Fin n, p ≠ q →
      swapXY (blockFam Λ s a' b' 0 n p q) = blockFam Λ s a' b' 0 n p q
        + (X (Sum.inl p) * X (Sum.inr q)) ^ 2 + (X (Sum.inl q) * X (Sum.inr p)) ^ 2 :=
    fun p q _ => swapXY_Gpoly_zero (hlin _ _) (fun u v w => halt _ _ u v w) s a' b' p q
      (fun c u v => hdiag _ _ c u v)
  have hgdiagz : ∀ p q : Fin n, p ≠ q → diagXY (blockFam Λ s a' b' 0 n p q) = 0 :=
    fun p q _ => diagXY_Gpoly_zero (hlin _ _) (fun u v w => halt _ _ u v w) s a' b'
  have hdet : (Matrix.of (blockFam Λ s a' b' 1 n)).det
      = ∑ σ ∈ PM (Fin n), (pfTerm (Matrix.of (blockFam Λ s a' b' 1 n)) σ) ^ 2 :=
    det_eq_sum_PM_sq _ hGsymm hGdiag
  have hperturb : ∀ σ ∈ PM (Fin n),
      (pfTerm (Matrix.of (blockFam Λ s a' b' 1 n)) σ).coeff
        (bal (Finset.univ : Finset (Fin n))) = 1 := by
    intro σ hσ
    have hmat : Matrix.of (blockFam Λ s a' b' 1 n)
        = Matrix.of (fun p q => blockFam Λ s a' b' 0 n p q
            + (blockFam Λ s a' b' 1 n p q - blockFam Λ s a' b' 0 n p q)) := by
      ext p q; simp
    rw [hmat, coeff_bal_pfTerm_perturb (blockFam Λ s a' b' 0 n)
      (fun p q => blockFam Λ s a' b' 1 n p q - blockFam Λ s a' b' 0 n p q) hghom hcdeg σ hσ]
    exact coeff_bal_prod_matching (blockFam Λ s a' b' 0 n) hgswap hgdiagz σ hσ
  have hgdeg : ∀ p q : Fin n, (blockFam Λ s a' b' 1 n p q).totalDegree ≤ 4 := by
    intro p q
    have h : blockFam Λ s a' b' 1 n p q
        = blockFam Λ s a' b' 0 n p q
          + (blockFam Λ s a' b' 1 n p q - blockFam Λ s a' b' 0 n p q) := by ring
    rw [h]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hghom p q).totalDegree_le ((hcdeg p q).trans (by norm_num)))
  -- the values of the determinant at the `0/1` points sum to `1`, so one of them has norm `≥ 1`
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n ⊕ Fin n → 𝕜, (∀ i, ‖z i‖ ≤ 1) ∧
      1 ≤ ‖eval z ((Matrix.of (blockFam Λ s a' b' 1 n)).det)‖ :=
    exists_cubePt_norm_det_ge_one (blockFam Λ s a' b' 1 n) hGsymm hGdiag hgdeg hperturb
      (by simpa using hn)
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin n → 𝕜, z = Sum.elim x y :=
    ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), by funext w; cases w <;> rfl⟩
  refine ⟨x, y, fun i => hz1 (Sum.inl i), fun i => hz1 (Sum.inr i), ?_⟩
  have heval : eval (Sum.elim x y) ((Matrix.of (blockFam Λ s a' b' 1 n)).det)
      = (Matrix.of fun p q : Fin n =>
          Λ (s + (p : ℕ)) (s + (q : ℕ)) (a' + blockVec s x) (b' + blockVec s y)
            (a' + blockVec s x) (b' + blockVec s y)).det := by
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, blockFam_apply]
    rw [eval_Gpoly (hlin _ _), one_smul, one_smul]
  rw [← heval]
  exact hz2

end AltCounter
