/-
The counterexample: over an ultrametric field `𝕜` of characteristic 2 with the multilinear Phillips
property (e.g. the completion of the field of `2`-power Puiseux series over `𝔽₂`), with `E = ℓ^∞(ℕ, 𝕜)` and
`F` the closed span of the matrices `x ⊗ y + y ⊗ x` in `ℓ^∞(ℕ × ℕ, 𝕜)`, the precomposition map
`f ↦ (m ↦ m ∘ (f, f))` on continuous alternating 2-forms is not analytic.
-/
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Algebra.CharP.Two
import AltCounter.Gluing
import AltCounter.Criterion

namespace AltCounter

open BoundedContinuousFunction

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- The matrix `x ⊗ y + y ⊗ x`, as a bounded function on `ℕ × ℕ`. -/
noncomputable def Wfun (x y : Linf 𝕜) : (ℕ × ℕ) →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun pq => x pq.1 * y pq.2 + y pq.1 * x pq.2) (2 * (‖x‖ * ‖y‖)) (by
      intro pq
      calc ‖x pq.1 * y pq.2 + y pq.1 * x pq.2‖
          ≤ ‖x pq.1 * y pq.2‖ + ‖y pq.1 * x pq.2‖ := norm_add_le _ _
        _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by
            gcongr
            · rw [norm_mul]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
            · rw [norm_mul, mul_comm]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
        _ = 2 * (‖x‖ * ‖y‖) := by ring)

/-- The closed linear span of the matrices `x ⊗ y + y ⊗ x`, as a submodule of `ℓ^∞(ℕ × ℕ)`. -/
noncomputable def FSub : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜) :=
  (Submodule.span 𝕜 (Set.range fun xy : Linf 𝕜 × Linf 𝕜 => Wfun 𝕜 xy.1 xy.2)).topologicalClosure

/-- The target space `F`: the closed linear span of the matrices `x ⊗ y + y ⊗ x`, as a normed space.
(A type synonym of the submodule, so that instance search treats it as an ordinary normed space.) -/
def F : Type _ := ↥(FSub 𝕜)

noncomputable instance : NormedAddCommGroup (F 𝕜) := inferInstanceAs (NormedAddCommGroup ↥(FSub 𝕜))
noncomputable instance : NormedSpace 𝕜 (F 𝕜) := inferInstanceAs (NormedSpace 𝕜 ↥(FSub 𝕜))

/-- The inclusion of `F` into `ℓ^∞(ℕ × ℕ)`. -/
noncomputable def F.incl : F 𝕜 →L[𝕜] ((ℕ × ℕ) →ᵇ 𝕜) := (FSub 𝕜).subtypeL

/-- The precomposition map on continuous alternating 2-forms `ℓ^∞ × ℓ^∞ → F`. -/
noncomputable def Q (f : Linf 𝕜 →L[𝕜] Linf 𝕜) :
    (Linf 𝕜) [⋀^Fin 2]→L[𝕜] (F 𝕜) →L[𝕜] (Linf 𝕜) [⋀^Fin 2]→L[𝕜] (F 𝕜) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM f

/-! ### Elementary facts about `Wfun`, `FSub` and `F` -/

@[simp] lemma Wfun_apply (x y : Linf 𝕜) (pq : ℕ × ℕ) :
    Wfun 𝕜 x y pq = x pq.1 * y pq.2 + y pq.1 * x pq.2 := rfl

lemma Wfun_mem (x y : Linf 𝕜) : Wfun 𝕜 x y ∈ FSub 𝕜 :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x, y), rfl⟩)

lemma F.incl_injective : Function.Injective (F.incl 𝕜) := Subtype.val_injective

lemma F.incl_mem (z : F 𝕜) : F.incl 𝕜 z ∈ FSub 𝕜 := (show ↥(FSub 𝕜) from z).2

lemma F.norm_incl (z : F 𝕜) : ‖F.incl 𝕜 z‖ = ‖z‖ := rfl

/-- The element of `F` given by `x ⊗ y + y ⊗ x`. -/
noncomputable def Welt (x y : Linf 𝕜) : F 𝕜 := (⟨Wfun 𝕜 x y, Wfun_mem 𝕜 x y⟩ : ↥(FSub 𝕜))

@[simp] lemma incl_Welt (x y : Linf 𝕜) : F.incl 𝕜 (Welt 𝕜 x y) = Wfun 𝕜 x y := rfl

/-! ### Symmetry and vanishing diagonal -/

/-- The submodule of symmetric matrices with vanishing diagonal. -/
def symSub : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜) where
  carrier := {g | (∀ p q : ℕ, g (p, q) = g (q, p)) ∧ ∀ p : ℕ, g (p, p) = 0}
  add_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    exact ⟨fun p q => by simp only [BoundedContinuousFunction.add_apply, hg1 p q, hh1 p q],
      fun p => by simp only [BoundedContinuousFunction.add_apply, hg2, hh2, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  smul_mem' := by
    rintro c g ⟨hg1, hg2⟩
    exact ⟨fun p q => by simp only [BoundedContinuousFunction.coe_smul, hg1 p q],
      fun p => by simp only [BoundedContinuousFunction.coe_smul, hg2, smul_zero]⟩

lemma continuous_bcfEval (z : ℕ × ℕ) :
    Continuous fun g : (ℕ × ℕ) →ᵇ 𝕜 => g z :=
  map_continuous (BoundedContinuousFunction.evalCLM 𝕜 z)

lemma isClosed_symSub : IsClosed ((symSub 𝕜 : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜)) : Set ((ℕ × ℕ) →ᵇ 𝕜)) := by
  have hset : ((symSub 𝕜 : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜)) : Set ((ℕ × ℕ) →ᵇ 𝕜)) =
      (⋂ p : ℕ, ⋂ q : ℕ, {g : (ℕ × ℕ) →ᵇ 𝕜 | g (p, q) = g (q, p)}) ∩
        (⋂ p : ℕ, {g : (ℕ × ℕ) →ᵇ 𝕜 | g (p, p) = 0}) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun p => isClosed_iInter fun q => ?_)
    (isClosed_iInter fun p => ?_)
  · exact isClosed_eq (continuous_bcfEval 𝕜 _) (continuous_bcfEval 𝕜 _)
  · exact isClosed_eq (continuous_bcfEval 𝕜 _) continuous_const

lemma Wfun_mem_symSub [CharP 𝕜 2] (x y : Linf 𝕜) : Wfun 𝕜 x y ∈ symSub 𝕜 := by
  constructor
  · intro p q; simp only [Wfun_apply]; ring
  · intro p
    simp only [Wfun_apply]
    rw [mul_comm (y p) (x p)]
    exact CharTwo.add_self_eq_zero _

lemma FSub_le_symSub [CharP 𝕜 2] : FSub 𝕜 ≤ symSub 𝕜 := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_symSub 𝕜)
  rw [Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact Wfun_mem_symSub 𝕜 x y

lemma FSub_symm [CharP 𝕜 2] {g : (ℕ × ℕ) →ᵇ 𝕜} (hg : g ∈ FSub 𝕜) (p q : ℕ) :
    g (p, q) = g (q, p) := (FSub_le_symSub 𝕜 hg).1 p q

lemma FSub_diag [CharP 𝕜 2] {g : (ℕ × ℕ) →ᵇ 𝕜} (hg : g ∈ FSub 𝕜) (p : ℕ) :
    g (p, p) = 0 := (FSub_le_symSub 𝕜 hg).2 p

/-! ### Finite-rank approximation -/

/-- `g` is uniformly approximable by finite-rank matrices. -/
def Approx (g : (ℕ × ℕ) →ᵇ 𝕜) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (r : ℕ) (u v : Fin r → ℕ → 𝕜),
    ∀ p q, ‖g (p, q) - ∑ k, u k p * v k q‖ ≤ η

/-- The submodule of uniformly finite-rank-approximable matrices. -/
def apxSub : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜) where
  carrier := {g | Approx 𝕜 g}
  add_mem' := by
    rintro g h hg hh η hη
    obtain ⟨r₁, u₁, v₁, h₁⟩ := hg (η / 2) (by linarith)
    obtain ⟨r₂, u₂, v₂, h₂⟩ := hh (η / 2) (by linarith)
    refine ⟨r₁ + r₂, Fin.append u₁ u₂, Fin.append v₁ v₂, fun p q => ?_⟩
    have hsum : ∑ k : Fin (r₁ + r₂), Fin.append u₁ u₂ k p * Fin.append v₁ v₂ k q
        = (∑ k, u₁ k p * v₁ k q) + ∑ k, u₂ k p * v₂ k q := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    rw [hsum]
    have : (g + h) (p, q) - ((∑ k, u₁ k p * v₁ k q) + ∑ k, u₂ k p * v₂ k q)
        = (g (p, q) - ∑ k, u₁ k p * v₁ k q) + (h (p, q) - ∑ k, u₂ k p * v₂ k q) := by
      simp only [BoundedContinuousFunction.add_apply]; ring
    rw [this]
    calc ‖(g (p, q) - ∑ k, u₁ k p * v₁ k q) + (h (p, q) - ∑ k, u₂ k p * v₂ k q)‖
        ≤ ‖g (p, q) - ∑ k, u₁ k p * v₁ k q‖ + ‖h (p, q) - ∑ k, u₂ k p * v₂ k q‖ := norm_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add (h₁ p q) (h₂ p q)
      _ = η := by ring
  zero_mem' := by
    intro η hη
    exact ⟨0, fun k => k.elim0, fun k => k.elim0, fun p q => by simp [le_of_lt hη]⟩
  smul_mem' := by
    rintro c g hg η hη
    obtain ⟨r, u, v, hr⟩ := hg (η / (‖c‖ + 1)) (by positivity)
    refine ⟨r, fun k p => c * u k p, v, fun p q => ?_⟩
    have hrw : (c • g) (p, q) - ∑ k, c * u k p * v k q
        = c * (g (p, q) - ∑ k, u k p * v k q) := by
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul,
        Finset.mul_sum, mul_sub, mul_assoc]
    rw [hrw, norm_mul]
    calc ‖c‖ * ‖g (p, q) - ∑ k, u k p * v k q‖ ≤ ‖c‖ * (η / (‖c‖ + 1)) := by
          gcongr; exact hr p q
      _ ≤ η := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg c, hη.le]

lemma isClosed_apxSub : IsClosed ((apxSub 𝕜 : Submodule 𝕜 ((ℕ × ℕ) →ᵇ 𝕜)) : Set ((ℕ × ℕ) →ᵇ 𝕜)) := by
  refine isClosed_of_closure_subset fun g hg η hη => ?_
  obtain ⟨g', hg', hd⟩ := Metric.mem_closure_iff.1 hg (η / 2) (by linarith)
  obtain ⟨r, u, v, hr⟩ := hg' (η / 2) (by linarith)
  refine ⟨r, u, v, fun p q => ?_⟩
  have h1 : ‖g (p, q) - g' (p, q)‖ ≤ η / 2 := by
    have := BoundedContinuousFunction.norm_coe_le_norm (g - g') (p, q)
    rw [BoundedContinuousFunction.sub_apply] at this
    refine this.trans ?_
    rw [← dist_eq_norm]
    exact hd.le
  have hrw : g (p, q) - ∑ k, u k p * v k q
      = (g (p, q) - g' (p, q)) + (g' (p, q) - ∑ k, u k p * v k q) := by ring
  rw [hrw]
  calc ‖(g (p, q) - g' (p, q)) + (g' (p, q) - ∑ k, u k p * v k q)‖
      ≤ ‖g (p, q) - g' (p, q)‖ + ‖g' (p, q) - ∑ k, u k p * v k q‖ := norm_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add h1 (hr p q)
    _ = η := by ring

lemma Wfun_mem_apxSub (x y : Linf 𝕜) : Wfun 𝕜 x y ∈ apxSub 𝕜 := by
  intro η hη
  refine ⟨2, ![fun p => x p, fun p => y p], ![fun q => y q, fun q => x q], fun p q => ?_⟩
  have : ∑ k : Fin 2, (![fun p => x p, fun p => y p] : Fin 2 → ℕ → 𝕜) k p *
      (![fun q => y q, fun q => x q] : Fin 2 → ℕ → 𝕜) k q = x p * y q + y p * x q := by
    simp [Fin.sum_univ_two]
  rw [Wfun_apply, this]
  simpa using hη.le

lemma FSub_le_apxSub : FSub 𝕜 ≤ apxSub 𝕜 := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_apxSub 𝕜)
  rw [Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact Wfun_mem_apxSub 𝕜 x y

lemma FSub_approx {g : (ℕ × ℕ) →ᵇ 𝕜} (hg : g ∈ FSub 𝕜) : Approx 𝕜 g := FSub_le_apxSub 𝕜 hg

/-! ### The alternating map `W₀` -/

lemma fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by revert i; decide

lemma fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

lemma fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

lemma update_fin2_zero {α : Type*} [DecidableEq (Fin 2)] (m : Fin 2 → α) (z : α) :
    Function.update m 0 z = ![z, m 1] := by
  ext j
  rcases fin_two_cases j with rfl | rfl
  · rw [Function.update_self]; simp
  · rw [Function.update_of_ne fin2_one_ne_zero]; simp

lemma update_fin2_one {α : Type*} [DecidableEq (Fin 2)] (m : Fin 2 → α) (z : α) :
    Function.update m 1 z = ![m 0, z] := by
  ext j
  rcases fin_two_cases j with rfl | rfl
  · rw [Function.update_of_ne fin2_zero_ne_one]; simp
  · rw [Function.update_self]; simp

lemma Welt_add_left (x x' y : Linf 𝕜) : Welt 𝕜 (x + x') y = Welt 𝕜 x y + Welt 𝕜 x' y := by
  apply F.incl_injective 𝕜
  rw [map_add, incl_Welt, incl_Welt, incl_Welt]
  ext pq
  simp only [Wfun_apply, BoundedContinuousFunction.add_apply]
  ring

lemma Welt_add_right (x y y' : Linf 𝕜) : Welt 𝕜 x (y + y') = Welt 𝕜 x y + Welt 𝕜 x y' := by
  apply F.incl_injective 𝕜
  rw [map_add, incl_Welt, incl_Welt, incl_Welt]
  ext pq
  simp only [Wfun_apply, BoundedContinuousFunction.add_apply]
  ring

lemma Welt_smul_left (c : 𝕜) (x y : Linf 𝕜) : Welt 𝕜 (c • x) y = c • Welt 𝕜 x y := by
  apply F.incl_injective 𝕜
  rw [map_smul, incl_Welt, incl_Welt]
  ext pq
  simp only [Wfun_apply, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  ring

lemma Welt_smul_right (c : 𝕜) (x y : Linf 𝕜) : Welt 𝕜 x (c • y) = c • Welt 𝕜 x y := by
  apply F.incl_injective 𝕜
  rw [map_smul, incl_Welt, incl_Welt]
  ext pq
  simp only [Wfun_apply, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  ring

/-- `W₀` as a multilinear map. -/
noncomputable def W₀m : MultilinearMap 𝕜 (fun _ : Fin 2 => Linf 𝕜) (F 𝕜) where
  toFun v := Welt 𝕜 (v 0) (v 1)
  map_update_add' := by
    intro _ m i x y
    rcases fin_two_cases i with rfl | rfl
    · simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact Welt_add_left 𝕜 _ _ _
    · simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact Welt_add_right 𝕜 _ _ _
  map_update_smul' := by
    intro _ m i c x
    rcases fin_two_cases i with rfl | rfl
    · simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact Welt_smul_left 𝕜 _ _ _
    · simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact Welt_smul_right 𝕜 _ _ _

/-- `W₀` as an alternating map (uses characteristic `2`). -/
noncomputable def W₀a [CharP 𝕜 2] : AlternatingMap 𝕜 (Linf 𝕜) (F 𝕜) (Fin 2) where
  toMultilinearMap := W₀m 𝕜
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have h01 : v 0 = v 1 := by
      rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;> simp_all
    show Welt 𝕜 (v 0) (v 1) = 0
    rw [← h01]
    apply F.incl_injective 𝕜
    rw [incl_Welt, map_zero]
    ext pq
    simp only [Wfun_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

lemma norm_Wfun_le (x y : Linf 𝕜) : ‖Wfun 𝕜 x y‖ ≤ 2 * (‖x‖ * ‖y‖) := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro pq
  rw [Wfun_apply]
  calc ‖x pq.1 * y pq.2 + y pq.1 * x pq.2‖
      ≤ ‖x pq.1 * y pq.2‖ + ‖y pq.1 * x pq.2‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by
        gcongr
        · rw [norm_mul]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
        · rw [norm_mul, mul_comm]; gcongr <;> exact BoundedContinuousFunction.norm_coe_le_norm _ _
    _ = 2 * (‖x‖ * ‖y‖) := by ring

lemma norm_Welt_le (x y : Linf 𝕜) : ‖Welt 𝕜 x y‖ ≤ 2 * (‖x‖ * ‖y‖) := by
  rw [← F.norm_incl 𝕜, incl_Welt]
  exact norm_Wfun_le 𝕜 x y

/-- The continuous alternating map `(x, y) ↦ x ⊗ y + y ⊗ x` with values in `F`. -/
noncomputable def W₀ [CharP 𝕜 2] : (Linf 𝕜) [⋀^Fin 2]→L[𝕜] (F 𝕜) :=
  (W₀a 𝕜).mkContinuous 2 (fun m => by
    show ‖Welt 𝕜 (m 0) (m 1)‖ ≤ 2 * ∏ i, ‖m i‖
    rw [Fin.prod_univ_two]
    exact norm_Welt_le 𝕜 _ _)

@[simp] lemma W₀_apply [CharP 𝕜 2] (v : Fin 2 → Linf 𝕜) : W₀ 𝕜 v = Welt 𝕜 (v 0) (v 1) := rfl

lemma norm_W₀_le [CharP 𝕜 2] : ‖W₀ 𝕜‖ ≤ 2 :=
  AlternatingMap.mkContinuous_norm_le _ (by norm_num) _

/-! ### Multiplication operators -/

/-- Pointwise multiplication by `a` as a continuous linear operator on `ℓ^∞`. -/
noncomputable def mulL (a : Linf 𝕜) : Linf 𝕜 →L[𝕜] Linf 𝕜 :=
  ContinuousLinearMap.mul 𝕜 (Linf 𝕜) a

@[simp] lemma mulL_apply (a x : Linf 𝕜) (p : ℕ) : mulL 𝕜 a x p = a p * x p := rfl

lemma mulL_add (a a' : Linf 𝕜) : mulL 𝕜 (a + a') = mulL 𝕜 a + mulL 𝕜 a' :=
  map_add (ContinuousLinearMap.mul 𝕜 (Linf 𝕜)) a a'

lemma mulL_smul (c : 𝕜) (a : Linf 𝕜) : mulL 𝕜 (c • a) = c • mulL 𝕜 a :=
  map_smul (ContinuousLinearMap.mul 𝕜 (Linf 𝕜)) c a

lemma norm_mulL_le (a : Linf 𝕜) : ‖mulL 𝕜 a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le 𝕜 (Linf 𝕜) a

/-! ### `Q` is homogeneous of degree `2` -/

lemma Q_homogeneous (c : 𝕜) (f : Linf 𝕜 →L[𝕜] Linf 𝕜) : Q 𝕜 (c • f) = c ^ 2 • Q 𝕜 f := by
  ext m v
  have key := (m.toAlternatingMap).map_smul_univ (fun _ : Fin 2 => c) (fun i => f (v i))
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at key
  show m (⇑(c • f) ∘ v) = c ^ 2 • m (⇑f ∘ v)
  simpa only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Function.comp_def] using key

variable {𝕜}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Main theorem.** `Q` is not analytic at `0`. -/
theorem not_analyticAt_Q [IsUltrametricDist 𝕜] [CharP 𝕜 2]
    (htail : TailProperty 𝕜) : ¬ AnalyticAt 𝕜 (Q 𝕜) 0 := by
  intro hQ
  obtain ⟨P, hP⟩ :=
    exists_bilinear_of_analyticAt_of_homogeneous (Q 𝕜) (fun c f => Q_homogeneous 𝕜 c f) hQ
  obtain ⟨M, hM⟩ : ∃ M : Linf 𝕜 → Linf 𝕜 → ((Linf 𝕜) [⋀^Fin 2]→L[𝕜] F 𝕜),
      ∀ a b, M a b = (P ![mulL 𝕜 a, mulL 𝕜 b]) (W₀ 𝕜) := ⟨_, fun _ _ => rfl⟩
  -- additivity and homogeneity of `M` in each of its two slots
  have hMadd₁ : ∀ a a' b, M (a + a') b = M a b + M a' b := by
    intro a a' b
    have h := P.map_update_add ![mulL 𝕜 a, mulL 𝕜 b] 0 (mulL 𝕜 a) (mulL 𝕜 a')
    simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hM, hM, hM, mulL_add, h, ContinuousLinearMap.add_apply]
  have hMadd₂ : ∀ a b b', M a (b + b') = M a b + M a b' := by
    intro a b b'
    have h := P.map_update_add ![mulL 𝕜 a, mulL 𝕜 b] 1 (mulL 𝕜 b) (mulL 𝕜 b')
    simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hM, hM, hM, mulL_add, h, ContinuousLinearMap.add_apply]
  have hMsmul₁ : ∀ (c : 𝕜) a b, M (c • a) b = c • M a b := by
    intro c a b
    have h := P.map_update_smul ![mulL 𝕜 a, mulL 𝕜 b] 0 c (mulL 𝕜 a)
    simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hM, hM, mulL_smul, h, ContinuousLinearMap.smul_apply]
  have hMsmul₂ : ∀ (c : 𝕜) a b, M a (c • b) = c • M a b := by
    intro c a b
    have h := P.map_update_smul ![mulL 𝕜 a, mulL 𝕜 b] 1 c (mulL 𝕜 b)
    simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hM, hM, mulL_smul, h, ContinuousLinearMap.smul_apply]
  -- the operator norm bound for `M`
  have hMnorm : ∀ a b, ‖M a b‖ ≤ (‖P‖ * ‖W₀ 𝕜‖) * (‖a‖ * ‖b‖) := by
    intro a b
    have h1 : ‖P ![mulL 𝕜 a, mulL 𝕜 b]‖ ≤ ‖P‖ * (‖a‖ * ‖b‖) := by
      refine (P.le_opNorm _).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_mulL_le 𝕜 a) (norm_mulL_le 𝕜 b) (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    calc ‖M a b‖ = ‖(P ![mulL 𝕜 a, mulL 𝕜 b]) (W₀ 𝕜)‖ := by rw [hM]
      _ ≤ ‖P ![mulL 𝕜 a, mulL 𝕜 b]‖ * ‖W₀ 𝕜‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖P‖ * (‖a‖ * ‖b‖)) * ‖W₀ 𝕜‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (‖P‖ * ‖W₀ 𝕜‖) * (‖a‖ * ‖b‖) := by ring
  -- apply the core contradiction
  refine core_false htail
    (fun p q a b x y => F.incl 𝕜 (M a b ![x, y]) (p, q))
    (max 1 (‖P‖ * ‖W₀ 𝕜‖)) (le_max_left _ _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro p q
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a a' b x y
      rw [hMadd₁, ContinuousAlternatingMap.add_apply, map_add,
        BoundedContinuousFunction.add_apply]
    · intro a b b' x y
      rw [hMadd₂, ContinuousAlternatingMap.add_apply, map_add,
        BoundedContinuousFunction.add_apply]
    · intro a b x x' y
      have h := (M a b).map_update_add ![x, y] 0 x x'
      simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at h
      rw [h, map_add, BoundedContinuousFunction.add_apply]
    · intro a b x y y'
      have h := (M a b).map_update_add ![x, y] 1 y y'
      simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at h
      rw [h, map_add, BoundedContinuousFunction.add_apply]
    · intro c a b x y
      rw [hMsmul₁, ContinuousAlternatingMap.smul_apply, map_smul]
      simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    · intro c a b x y
      rw [hMsmul₂, ContinuousAlternatingMap.smul_apply, map_smul]
      simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    · intro c a b x y
      have h := (M a b).map_update_smul ![x, y] 0 c x
      simp only [update_fin2_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at h
      rw [h, map_smul]
      simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    · intro c a b x y
      have h := (M a b).map_update_smul ![x, y] 1 c y
      simp only [update_fin2_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at h
      rw [h, map_smul]
      simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    · intro a b x y
      calc ‖F.incl 𝕜 (M a b ![x, y]) (p, q)‖
          ≤ ‖F.incl 𝕜 (M a b ![x, y])‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ = ‖M a b ![x, y]‖ := F.norm_incl 𝕜 _
        _ ≤ ‖M a b‖ * (‖x‖ * ‖y‖) := by
            refine ((M a b).le_opNorm _).trans_eq ?_
            rw [Fin.prod_univ_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        _ ≤ ((‖P‖ * ‖W₀ 𝕜‖) * (‖a‖ * ‖b‖)) * (‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_right (hMnorm a b) (by positivity)
        _ = (‖P‖ * ‖W₀ 𝕜‖) * (‖a‖ * ‖b‖ * (‖x‖ * ‖y‖)) := by ring
        _ ≤ (max 1 (‖P‖ * ‖W₀ 𝕜‖)) * (‖a‖ * ‖b‖ * (‖x‖ * ‖y‖)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = (max 1 (‖P‖ * ‖W₀ 𝕜‖)) * ‖a‖ * ‖b‖ * ‖x‖ * ‖y‖ := by ring
  · -- alternating in the last two slots
    intro p q a b x
    have h : M a b ![x, x] = 0 :=
      ContinuousAlternatingMap.map_eq_zero_of_eq (M a b) ![x, x]
        (i := 0) (j := 1) (by simp) fin2_zero_ne_one
    rw [h, map_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  · -- diagonal values
    intro p q a x y
    have hconst : ![mulL 𝕜 a, mulL 𝕜 a] = fun _ : Fin 2 => mulL 𝕜 a := by
      funext i; rcases fin_two_cases i with rfl | rfl <;> simp
    have h : M a a = (Q 𝕜 (mulL 𝕜 a)) (W₀ 𝕜) := by rw [hM, hconst, hP]
    rw [h]
    show F.incl 𝕜 (W₀ 𝕜 (⇑(mulL 𝕜 a) ∘ ![x, y])) (p, q) = _
    rw [W₀_apply, incl_Welt, Wfun_apply]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mulL_apply]
  · -- symmetry
    intro p q a b x y
    exact FSub_symm 𝕜 (F.incl_mem 𝕜 _) p q
  · -- vanishing diagonal
    intro p a b x y
    exact FSub_diag 𝕜 (F.incl_mem 𝕜 _) p
  · -- finite-rank approximation
    intro a b x y η hη
    exact FSub_approx 𝕜 (F.incl_mem 𝕜 _) η hη

/-- In particular `Q` is not `C^ω`: the restriction to `n : ℕ∞` in the smooth statement is sharp. -/
theorem not_contDiff_omega_Q [IsUltrametricDist 𝕜] [CharP 𝕜 2]
    (htail : TailProperty 𝕜) : ¬ ContDiff 𝕜 (⊤ : WithTop ℕ∞) (Q 𝕜) := fun h =>
  not_analyticAt_Q htail (h.analyticOnNhd (s := Set.univ) 0 (Set.mem_univ 0))

end AltCounter
