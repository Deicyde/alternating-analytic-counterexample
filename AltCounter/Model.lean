/-
From a (not necessarily complete) field `L` with a nonarchimedean absolute value having the right properties to a
complete normed field with the same properties: pass to the completion.
-/
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra
import AltCounter.NestedBalls

namespace AltCounter

/-- A field with a nonarchimedean, nontrivial absolute value, of characteristic 2, with "infinite residue field", and
with a nested sequence of closed balls (radii strictly decreasing and bounded below by some `ρ > 0`) having empty
intersection. -/
structure IsGoodModel {L : Type} [Field L] (v : AbsoluteValue L ℝ) : Prop where
  char2 : CharP L 2
  nonarch : IsNonarchimedean v
  nontriv : ∃ x, 1 < v x
  residue : ∀ N : ℕ, ∃ t : Fin N → L, (∀ i, v (t i) ≤ 1) ∧ ∀ i j, i ≠ j → v (t i - t j) = 1
  balls : ∃ (c : ℕ → L) (r : ℕ → ℝ) (ρ : ℝ), 0 < ρ ∧ (∀ n, ρ ≤ r n) ∧ StrictAnti r ∧
    (∀ n, v (c (n + 1) - c n) ≤ r n) ∧ ∀ a : L, ∃ n, r n < v (a - c n)

section GoodModel

open UniformSpace

variable {L : Type} [Field L] {v : AbsoluteValue L ℝ}

/-- The completion of `WithAbs v`; the field the counterexample runs on. -/
private abbrev Cpl (v : AbsoluteValue L ℝ) := UniformSpace.Completion (WithAbs v)

private lemma norm_toAbs (x : L) : ‖WithAbs.toAbs v x‖ = v x := rfl

private lemma norm_coe_toAbs (x : L) : ‖((WithAbs.toAbs v x : WithAbs v) : Cpl v)‖ = v x :=
  Completion.norm_coe _

private lemma norm_coe_toAbs_sub (x y : L) :
    ‖((WithAbs.toAbs v x : WithAbs v) : Cpl v) - ((WithAbs.toAbs v y : WithAbs v) : Cpl v)‖
      = v (x - y) := by
  rw [← Completion.coe_sub, Completion.norm_coe]
  rfl

/-- The absolute value being nonarchimedean means exactly that `WithAbs v` is ultrametric. -/
private lemma withAbs_ultrametric (hv : IsGoodModel v) : IsUltrametricDist (WithAbs v) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (fun x y => hv.nonarch x.ofAbs y.ofAbs)

/-- Ultrametricity passes to the completion, by density. -/
private lemma completion_ultrametric (hv : IsGoodModel v) : IsUltrametricDist (Cpl v) := by
  have := withAbs_ultrametric hv
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y => ?_)
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
      rw [← Completion.coe_add, Completion.norm_coe, Completion.norm_coe, Completion.norm_coe]
      exact IsUltrametricDist.norm_add_le_max a b

private lemma withAbs_charP (hv : IsGoodModel v) : CharP (WithAbs v) 2 :=
  haveI := hv.char2
  charP_of_injective_ringHom (f := (WithAbs.equiv v).symm.toRingHom)
    (WithAbs.equiv v).symm.injective 2

private lemma completion_charP (hv : IsGoodModel v) : CharP (Cpl v) 2 :=
  haveI := withAbs_charP hv
  charP_of_injective_ringHom (f := Completion.coeRingHom)
    (Completion.coe_injective (α := WithAbs v)) 2

/-- The residue field stays infinite: the coercion is isometric. -/
private lemma completion_residue (hv : IsGoodModel v) :
    ∀ N : ℕ, ∃ t : Fin N → Cpl v, (∀ i, ‖t i‖ ≤ 1) ∧ ∀ i j, i ≠ j → ‖t i - t j‖ = 1 := by
  intro N
  obtain ⟨t, ht1, ht2⟩ := hv.residue N
  refine ⟨fun i => ((WithAbs.toAbs v (t i) : WithAbs v) : Cpl v), fun i => ?_, fun i j hij => ?_⟩
  · rw [norm_coe_toAbs]; exact ht1 i
  · rw [norm_coe_toAbs_sub]; exact ht2 i j hij

/-- The nested balls with empty intersection survive in the completion: take the same centres and radii.
Emptiness uses that `L` is dense in its completion together with the ultrametric inequality. -/
private lemma completion_balls (hv : IsGoodModel v) :
    ∃ (c : ℕ → Cpl v) (r : ℕ → ℝ), StrictAnti r ∧ (∀ n, ‖c (n + 1) - c n‖ ≤ r n) ∧
      ∀ a : Cpl v, ∃ n, r n < ‖a - c n‖ := by
  have := completion_ultrametric hv
  obtain ⟨c, r, ρ, hρ, hρr, hanti, hnest, hempty⟩ := hv.balls
  refine ⟨fun n => ((WithAbs.toAbs v (c n) : WithAbs v) : Cpl v), r, hanti, fun n => ?_, fun a => ?_⟩
  · rw [norm_coe_toAbs_sub]; exact hnest n
  -- emptiness
  obtain ⟨y, hy⟩ := Completion.denseRange_coe.exists_dist_lt a hρ
  obtain ⟨n, hn⟩ := hempty y.ofAbs
  refine ⟨n, ?_⟩
  rcases lt_or_ge (r n) ‖a - ((WithAbs.toAbs v (c n) : WithAbs v) : Cpl v)‖ with h | h
  · exact h
  exfalso
  set K := ((WithAbs.toAbs v (c n) : WithAbs v) : Cpl v) with hK
  -- `hn`, transported to the completion
  have hn' : r n < ‖((y : Cpl v)) - K‖ := by
    have : ((y : Cpl v)) - K = ((WithAbs.toAbs v y.ofAbs : WithAbs v) : Cpl v) - K := rfl
    rw [this, hK, norm_coe_toAbs_sub]
    exact hn
  -- the ultrametric inequality in the completion
  have hsplit : ((y : Cpl v)) - K = (((y : Cpl v)) - a) + (a - K) := by ring
  have hmax : ‖((y : Cpl v)) - K‖ ≤ max ‖((y : Cpl v)) - a‖ ‖a - K‖ := by
    rw [hsplit]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hya : ‖((y : Cpl v)) - a‖ < ρ := by
    rw [← dist_eq_norm, dist_comm]
    exact hy
  have : ‖((y : Cpl v)) - K‖ ≤ r n :=
    hmax.trans (max_le (le_of_lt (hya.trans_le (hρr n))) h)
  exact absurd this (not_le.2 hn')

end GoodModel

/-- The completion of a good model is a complete ultrametric nontrivially normed field of characteristic 2 with
infinite residue field which is not spherically complete. -/
theorem exists_field_of_goodModel {L : Type} [Field L] (v : AbsoluteValue L ℝ) (hv : IsGoodModel v) :
    ∃ (K : Type) (_ : NontriviallyNormedField K), IsUltrametricDist K ∧ CompleteSpace K ∧ CharP K 2 ∧
      InfiniteResidue K ∧ HasEmptyNestedBalls K := by
  obtain ⟨x₀, hx₀⟩ := hv.nontriv
  exact ⟨UniformSpace.Completion (WithAbs v),
    { (inferInstance : NormedField (UniformSpace.Completion (WithAbs v))) with
        non_trivial := ⟨((WithAbs.toAbs v x₀ : WithAbs v) : UniformSpace.Completion (WithAbs v)),
          by rw [UniformSpace.Completion.norm_coe]; exact hx₀⟩ },
    completion_ultrametric hv,
    (inferInstance : CompleteSpace (UniformSpace.Completion (WithAbs v))),
    completion_charP hv, completion_residue hv, completion_balls hv⟩

end AltCounter
