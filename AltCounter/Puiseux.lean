/-
A concrete good model: the field of "2-power Puiseux series" `⋃_j κ((t^{1/2^j}))`, realised as a directed union of
subfields of the Hahn series field `HahnSeries ℚ κ` over an infinite field `κ` of characteristic 2, with the `t`-adic
absolute value `‖f‖ = 2 ^ (-order f)`.
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import AltCounter.Model

namespace AltCounter

namespace Puiseux

open HahnSeries

/-- The coefficient field: an algebraic closure of `𝔽₂`.  It is an infinite field of characteristic `2`. -/
abbrev Coeff : Type := AlgebraicClosure (ZMod 2)

/-- The ambient Hahn series field `κ⟦ℚ⟧`. -/
abbrev Ser : Type := HahnSeries ℚ Coeff

/-! ### The `t`-adic absolute value on `κ⟦ℚ⟧` -/

open scoped Classical in
/-- `v f = 2 ^ (-order f)`, and `v 0 = 0`. -/
noncomputable def vFun (x : Ser) : ℝ := if x = 0 then 0 else (2 : ℝ) ^ (-(x.order : ℝ))

@[simp] lemma vFun_zero : vFun 0 = 0 := by simp [vFun]

lemma vFun_of_ne {x : Ser} (hx : x ≠ 0) : vFun x = (2 : ℝ) ^ (-(x.order : ℝ)) := by
  simp [vFun, hx]

lemma vFun_pos {x : Ser} (hx : x ≠ 0) : 0 < vFun x := by
  rw [vFun_of_ne hx]; positivity

lemma vFun_nonneg (x : Ser) : 0 ≤ vFun x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (vFun_pos hx).le

lemma vFun_eq_zero_iff (x : Ser) : vFun x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (vFun_pos hx).ne' h
  · rintro rfl; simp

lemma vFun_mul (x y : Ser) : vFun (x * y) = vFun x * vFun y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hord : (x * y).order = x.order + y.order :=
    order_mul_of_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hx) (leadingCoeff_ne_zero.mpr hy))
  rw [vFun_of_ne hxy, vFun_of_ne hx, vFun_of_ne hy, hord]
  push_cast
  rw [neg_add, Real.rpow_add (by norm_num)]

lemma two_rpow_monotone : Monotone (fun t : ℝ => (2 : ℝ) ^ t) := fun _ _ hab =>
  Real.rpow_le_rpow_of_exponent_le (by norm_num) hab

lemma vFun_isNonarch : IsNonarchimedean vFun := by
  intro x y
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add]; exact le_max_right _ _
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]; exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, vFun_zero]
    exact le_max_of_le_left (vFun_nonneg x)
  have h := min_order_le_order_add (x := x) (y := y) hxy
  have hcast : ((min x.order y.order : ℚ) : ℝ) ≤ ((x + y).order : ℝ) := by exact_mod_cast h
  rw [vFun_of_ne hxy, vFun_of_ne hx, vFun_of_ne hy]
  have hexp : -((x + y).order : ℝ) ≤ max (-(x.order : ℝ)) (-(y.order : ℝ)) := by
    rcases le_total x.order y.order with h1 | h1
    · rw [min_eq_left h1] at hcast
      exact le_trans (by linarith) (le_max_left _ _)
    · rw [min_eq_right h1] at hcast
      exact le_trans (by linarith) (le_max_right _ _)
  calc (2 : ℝ) ^ (-((x + y).order : ℝ))
      ≤ (2 : ℝ) ^ (max (-(x.order : ℝ)) (-(y.order : ℝ))) := two_rpow_monotone hexp
    _ = max ((2 : ℝ) ^ (-(x.order : ℝ))) ((2 : ℝ) ^ (-(y.order : ℝ))) :=
        two_rpow_monotone.map_max

lemma vFun_add_le (x y : Ser) : vFun (x + y) ≤ vFun x + vFun y :=
  (vFun_isNonarch x y).trans (max_le (by linarith [vFun_nonneg y]) (by linarith [vFun_nonneg x]))

/-- The `t`-adic absolute value on `κ⟦ℚ⟧`. -/
noncomputable def vSer : AbsoluteValue Ser ℝ where
  toFun := vFun
  map_mul' := vFun_mul
  nonneg' := vFun_nonneg
  eq_zero' := vFun_eq_zero_iff
  add_le' := vFun_add_le

@[simp] lemma vSer_apply (x : Ser) : vSer x = vFun x := rfl

/-! ### The subfield of `2`-power Puiseux series -/

/-- `n ↦ n / 2 ^ j`, as an additive monoid hom `ℤ →+ ℚ`. -/
def dyad (j : ℕ) : ℤ →+ ℚ where
  toFun n := (n : ℚ) / 2 ^ j
  map_zero' := by simp
  map_add' a b := by push_cast; ring

@[simp] lemma dyad_apply (j : ℕ) (n : ℤ) : dyad j n = (n : ℚ) / 2 ^ j := rfl

lemma dyad_injective (j : ℕ) : Function.Injective (dyad j) := by
  intro a b hab
  have h2 : (2 : ℚ) ^ j ≠ 0 := by positivity
  rw [dyad_apply, dyad_apply] at hab
  field_simp at hab
  exact_mod_cast hab

lemma dyad_le_iff (j : ℕ) (a b : ℤ) : dyad j a ≤ dyad j b ↔ a ≤ b := by
  have h : (0 : ℚ) < 2 ^ j := by positivity
  rw [dyad_apply, dyad_apply, div_le_div_iff_of_pos_right h]
  exact_mod_cast Iff.rfl

/-- `ℤ ↪o ℚ`, `n ↦ n / 2 ^ j`. -/
def dyadEmb (j : ℕ) : ℤ ↪o ℚ := ⟨⟨dyad j, dyad_injective j⟩, dyad_le_iff j _ _⟩

@[simp] lemma dyadEmb_apply (j : ℕ) (n : ℤ) : dyadEmb j n = (n : ℚ) / 2 ^ j := rfl

/-- The `j`-th embedding `κ⟦ℤ⟧ →+* κ⟦ℚ⟧`, sending `t` to `t ^ (1 / 2 ^ j)`. -/
noncomputable def emb (j : ℕ) : HahnSeries ℤ Coeff →+* Ser :=
  embDomainRingHom (dyad j) (dyad_injective j) (dyad_le_iff j)

lemma emb_apply (j : ℕ) (x : HahnSeries ℤ Coeff) : emb j x = embDomain (dyadEmb j) x := rfl

lemma coeff_emb (j : ℕ) (x : HahnSeries ℤ Coeff) (n : ℤ) :
    (emb j x).coeff ((n : ℚ) / 2 ^ j) = x.coeff n := by
  have h := embDomain_coeff (f := dyadEmb j) (x := x) (a := n)
  rw [dyadEmb_apply] at h
  rw [emb_apply]
  exact h

lemma coeff_emb_of_forall_ne (j : ℕ) (x : HahnSeries ℤ Coeff) (q : ℚ)
    (hq : ∀ n : ℤ, (n : ℚ) / 2 ^ j ≠ q) : (emb j x).coeff q = 0 := by
  rw [emb_apply]
  refine embDomain_of_notMem_range ?_
  rintro ⟨n, hn⟩
  exact hq n (by rw [← hn, dyadEmb_apply])

/-- Doubling, as an order embedding `ℤ ↪o ℤ`. -/
def dblEmb : ℤ ↪o ℤ :=
  ⟨⟨fun n => 2 * n, fun a b hab => by
      have h : 2 * a = 2 * b := hab
      omega⟩, by
    intro a b
    show 2 * a ≤ 2 * b ↔ a ≤ b
    omega⟩

@[simp] lemma dblEmb_apply (n : ℤ) : dblEmb n = 2 * n := rfl

/-- The embeddings are compatible: `emb j` factors through `emb (j+1)`. -/
lemma emb_succ (j : ℕ) (x : HahnSeries ℤ Coeff) :
    emb j x = emb (j + 1) (embDomain dblEmb x) := by
  ext q
  by_cases hq : ∃ n : ℤ, (n : ℚ) / 2 ^ j = q
  · obtain ⟨n, rfl⟩ := hq
    have hq2 : ((n : ℚ)) / 2 ^ j = ((2 * n : ℤ) : ℚ) / 2 ^ (j + 1) := by push_cast; ring
    rw [coeff_emb, hq2, coeff_emb]
    have := embDomain_coeff (f := dblEmb) (x := x) (a := n)
    rw [dblEmb_apply] at this
    exact this.symm
  · push Not at hq
    rw [coeff_emb_of_forall_ne j x q hq]
    by_cases hq' : ∃ m : ℤ, (m : ℚ) / 2 ^ (j + 1) = q
    · obtain ⟨m, rfl⟩ := hq'
      rw [coeff_emb]
      refine (embDomain_of_notMem_range ?_).symm
      rintro ⟨n, hn⟩
      rw [dblEmb_apply] at hn
      exact hq n (by rw [← hn]; push_cast; ring)
    · push Not at hq'
      rw [coeff_emb_of_forall_ne (j + 1) _ q hq']

lemma fieldRange_mono : Monotone fun j : ℕ => (emb j).fieldRange := by
  refine monotone_nat_of_le_succ fun j => ?_
  rintro y ⟨x, rfl⟩
  exact ⟨embDomain dblEmb x, (emb_succ j x).symm⟩

/-- The field of `2`-power Puiseux series, as a subfield of `κ⟦ℚ⟧`. -/
noncomputable def P : Subfield Ser := ⨆ j : ℕ, (emb j).fieldRange

lemma mem_P (j : ℕ) (x : HahnSeries ℤ Coeff) : emb j x ∈ P :=
  le_iSup (fun j : ℕ => (emb j).fieldRange) j ⟨x, rfl⟩

lemma exists_of_mem_P {y : Ser} (hy : y ∈ P) : ∃ (j : ℕ) (x : HahnSeries ℤ Coeff), emb j x = y := by
  rw [P, Subfield.mem_iSup_of_directed fieldRange_mono.directed_le] at hy
  obtain ⟨j, x, hx⟩ := hy
  exact ⟨j, x, hx⟩

/-! ### Elements of `P` -/

lemma single_mem_P (j : ℕ) (n : ℤ) (r : Coeff) : single ((n : ℚ) / 2 ^ j) r ∈ P := by
  have h : emb j (single n r) = single ((n : ℚ) / 2 ^ j) r := by
    rw [emb_apply, embDomain_single, dyadEmb_apply]
  exact h ▸ mem_P j (single n r)

lemma single_mem_P' {q : ℚ} (j : ℕ) (n : ℤ) (h : (n : ℚ) / 2 ^ j = q) (r : Coeff) :
    single q r ∈ P := h ▸ single_mem_P j n r

lemma C_mem_P (r : Coeff) : (C r : Ser) ∈ P := by
  have h := single_mem_P' 0 0 (by norm_num : ((0 : ℤ) : ℚ) / 2 ^ (0 : ℕ) = (0 : ℚ)) r
  rwa [← C_apply] at h

lemma vFun_single {q : ℚ} {r : Coeff} (hr : r ≠ 0) : vFun (single q r) = (2 : ℝ) ^ (-(q : ℝ)) := by
  rw [vFun_of_ne (single_ne_zero hr), order_single hr]

/-! ### The model field -/

/-- The model: the field of `2`-power Puiseux series over `κ`. -/
abbrev L : Type := P

/-- The `t`-adic absolute value on the model. -/
noncomputable def vL : AbsoluteValue L ℝ where
  toFun x := vFun (x : Ser)
  map_mul' x y := by rw [Subfield.coe_mul, vFun_mul]
  nonneg' x := vFun_nonneg _
  eq_zero' x := by
    rw [vFun_eq_zero_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  add_le' x y := by rw [Subfield.coe_add]; exact vFun_add_le _ _

@[simp] lemma vL_apply (x : L) : vL x = vFun (x : Ser) := rfl

instance : CharP Ser 2 := charP_of_injective_ringHom (f := (C : Coeff →+* Ser)) C_injective 2

instance : CharP L 2 := RingHom.charP P.subtype Subtype.coe_injective 2

lemma vL_nonarch : IsNonarchimedean vL := by
  intro x y
  simpa [Subfield.coe_add] using vFun_isNonarch (x : Ser) (y : Ser)

/-! ### Nontriviality and the infinite residue field -/

lemma vL_nontriv : ∃ x : L, 1 < vL x := by
  refine ⟨⟨single (-1 : ℚ) 1, single_mem_P' 0 (-1) (by norm_num) 1⟩, ?_⟩
  rw [vL_apply]
  have : vFun (single (-1 : ℚ) (1 : Coeff)) = (2 : ℝ) ^ (1 : ℝ) := by
    rw [vFun_single one_ne_zero]; norm_num
  rw [show ((⟨single (-1 : ℚ) 1, _⟩ : L) : Ser) = single (-1 : ℚ) (1 : Coeff) from rfl, this,
    Real.rpow_one]
  norm_num

lemma vFun_C_eq_one {r : Coeff} (hr : r ≠ 0) : vFun (C r : Ser) = 1 := by
  rw [C_apply, vFun_single hr]
  norm_num

lemma vL_residue (N : ℕ) :
    ∃ t : Fin N → L, (∀ i, vL (t i) ≤ 1) ∧ ∀ i j, i ≠ j → vL (t i - t j) = 1 := by
  set k : Fin N → Coeff := fun i => Infinite.natEmbedding Coeff (i : ℕ) with hk
  have hkinj : Function.Injective k := fun i j hij => by
    have := (Infinite.natEmbedding Coeff).injective hij
    exact Fin.ext this
  refine ⟨fun i => ⟨C (k i), C_mem_P _⟩, fun i => ?_, fun i j hij => ?_⟩
  · rw [vL_apply]
    rcases eq_or_ne (k i) 0 with h | h
    · rw [show ((⟨C (k i), _⟩ : L) : Ser) = C (k i) from rfl, h, map_zero, vFun_zero]
      norm_num
    · rw [show ((⟨C (k i), _⟩ : L) : Ser) = C (k i) from rfl, vFun_C_eq_one h]
  · rw [vL_apply, Subfield.coe_sub,
      show ((⟨C (k i), _⟩ : L) : Ser) = C (k i) from rfl,
      show ((⟨C (k j), _⟩ : L) : Ser) = C (k j) from rfl, ← map_sub]
    exact vFun_C_eq_one (sub_ne_zero.mpr fun h => hij (hkinj h))

/-! ### The nested balls -/

/-- The exponents `γ m = 1 - 2 ^ (-(m+1))`, an increasing sequence of rationals with denominators
`2 ^ (m+1)`, converging to `1`. -/
def γ (m : ℕ) : ℚ := 1 - (1 / 2) ^ (m + 1)

lemma γ_dyadic (m : ℕ) : ((2 ^ (m + 1) - 1 : ℤ) : ℚ) / 2 ^ (m + 1) = γ m := by
  have h : (0 : ℚ) < 2 ^ (m + 1) := by positivity
  rw [γ, div_pow, one_pow]
  push_cast
  field_simp

lemma γ_lt_one (m : ℕ) : γ m < 1 := by
  have : (0 : ℚ) < (1 / 2 : ℚ) ^ (m + 1) := by positivity
  simp only [γ]; linarith

lemma γ_lt_succ (m : ℕ) : γ m < γ (m + 1) := by
  have hp : (0 : ℚ) < (1 / 2 : ℚ) ^ (m + 1) := by positivity
  have h : (1 / 2 : ℚ) ^ (m + 1 + 1) = (1 / 2 : ℚ) ^ (m + 1) * (1 / 2) := by ring
  simp only [γ]
  rw [h]
  linarith

lemma γ_strictMono : StrictMono γ := strictMono_nat_of_lt_succ γ_lt_succ

/-- `γ j` has denominator `2 ^ (j+1)` in lowest terms, so it is not of the form `n / 2 ^ j`. -/
lemma γ_not_dyadic (j : ℕ) (n : ℤ) : (n : ℚ) / 2 ^ j ≠ γ j := by
  intro h
  rw [← γ_dyadic j] at h
  have h2 : ((2 : ℚ) ^ j) ≠ 0 := by positivity
  have h3 : ((2 : ℚ) ^ (j + 1)) ≠ 0 := by positivity
  rw [div_eq_div_iff h2 h3] at h
  push_cast at h
  have h5 : ((2 : ℚ) * n) * 2 ^ j = (2 * 2 ^ j - 1) * 2 ^ j := by linear_combination h
  have h6 : (2 : ℚ) * n = 2 * 2 ^ j - 1 := mul_right_cancel₀ h2 h5
  have h7 : ((2 * n : ℤ) : ℚ) = ((2 * 2 ^ j - 1 : ℤ) : ℚ) := by push_cast; linarith
  have h8 : (2 * n : ℤ) = 2 * 2 ^ j - 1 := by exact_mod_cast h7
  obtain ⟨A, hA⟩ : ∃ A : ℤ, (2 : ℤ) ^ j = A := ⟨_, rfl⟩
  rw [hA] at h8
  omega

/-- The centres of the nested balls: partial sums of `∑ t ^ (γ m)`. -/
noncomputable def cSer (n : ℕ) : Ser := ∑ m ∈ Finset.range (n + 1), single (γ m) (1 : Coeff)

lemma cSer_mem (n : ℕ) : cSer n ∈ P :=
  sum_mem fun m _ => single_mem_P' (m + 1) (2 ^ (m + 1) - 1) (γ_dyadic m) 1

lemma cSer_succ_sub (n : ℕ) : cSer (n + 1) - cSer n = single (γ (n + 1)) (1 : Coeff) := by
  rw [cSer, cSer, Finset.sum_range_succ]
  abel

lemma coeff_cSer_self (n : ℕ) : (cSer n).coeff (γ n) = 1 := by
  rw [cSer, coeff_sum, Finset.sum_eq_single n]
  · rw [coeff_single_same]
  · intro b _ hbn
    exact coeff_single_of_ne fun h => hbn (γ_strictMono.injective h).symm
  · intro h
    exact absurd (Finset.self_mem_range_succ n) h

/-- The centres, as elements of the model. -/
noncomputable def cL (n : ℕ) : L := ⟨cSer n, cSer_mem n⟩

/-- The radii. -/
noncomputable def rad (n : ℕ) : ℝ := (2 : ℝ) ^ (-(γ (n + 1) : ℝ))

lemma rad_strictAnti : StrictAnti rad := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rw [rad, rad, Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  have := γ_lt_succ (n + 1)
  have : (γ (n + 1) : ℝ) < (γ (n + 1 + 1) : ℝ) := by exact_mod_cast this
  linarith

lemma half_le_rad (n : ℕ) : (1 / 2 : ℝ) ≤ rad n := by
  have h1 : ((γ (n + 1) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (γ_lt_one (n + 1)).le
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-(γ (n + 1) : ℝ)) :=
    two_rpow_monotone (by linarith)
  rw [Real.rpow_neg_one] at h2
  rw [rad]
  linarith [h2]

lemma vL_cL_succ_sub (n : ℕ) : vL (cL (n + 1) - cL n) ≤ rad n := by
  rw [vL_apply, Subfield.coe_sub]
  rw [show ((cL (n + 1) : L) : Ser) = cSer (n + 1) from rfl,
    show ((cL n : L) : Ser) = cSer n from rfl, cSer_succ_sub, vFun_single one_ne_zero, rad]

lemma vL_balls_empty (a : L) : ∃ n, rad n < vL (a - cL n) := by
  obtain ⟨j, x, hx⟩ := exists_of_mem_P a.2
  refine ⟨j, ?_⟩
  have ha : (a : Ser).coeff (γ j) = 0 := by
    rw [← hx]
    exact coeff_emb_of_forall_ne j x (γ j) (γ_not_dyadic j)
  have hc : ((a : Ser) - cSer j).coeff (γ j) = -1 := by
    rw [coeff_sub, ha, coeff_cSer_self, zero_sub]
  have hne0 : ((a : Ser) - cSer j) ≠ 0 :=
    ne_zero_of_coeff_ne_zero (by rw [hc]; exact neg_ne_zero.mpr one_ne_zero)
  have horder : ((a : Ser) - cSer j).order ≤ γ j :=
    order_le_of_coeff_ne_zero (by rw [hc]; exact neg_ne_zero.mpr one_ne_zero)
  have hcast : (((a : Ser) - cSer j).order : ℝ) ≤ (γ j : ℝ) := by exact_mod_cast horder
  have h1 : (2 : ℝ) ^ (-(γ j : ℝ)) ≤ vL (a - cL j) := by
    rw [vL_apply, Subfield.coe_sub, show ((cL j : L) : Ser) = cSer j from rfl, vFun_of_ne hne0]
    exact two_rpow_monotone (by linarith)
  have h2 : rad j < (2 : ℝ) ^ (-(γ j : ℝ)) := by
    rw [rad, Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    have : (γ j : ℝ) < (γ (j + 1) : ℝ) := by exact_mod_cast γ_lt_succ j
    linarith
  linarith

theorem isGoodModel : IsGoodModel vL where
  char2 := inferInstance
  nonarch := vL_nonarch
  nontriv := vL_nontriv
  residue := vL_residue
  balls := ⟨cL, rad, 1 / 2, by norm_num, half_le_rad, rad_strictAnti, vL_cL_succ_sub,
    vL_balls_empty⟩

end Puiseux

theorem exists_goodModel : ∃ (L : Type) (_ : Field L) (v : AbsoluteValue L ℝ), IsGoodModel v :=
  ⟨Puiseux.L, inferInstance, Puiseux.vL, Puiseux.isGoodModel⟩

end AltCounter
