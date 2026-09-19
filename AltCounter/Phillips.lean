/-
Tails of bounded multilinear forms on `ℓ^∞` of arbitrary arity, from the one-variable case, and the
Phillips property `TailProperty` used in the main theorem.
-/
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import AltCounter.PhillipsOne

namespace AltCounter

open BoundedContinuousFunction Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A function of `d` arguments in `ℓ^∞` which is additive and homogeneous in each argument and bounded. -/
structure IsBddML {d : ℕ} (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ) : Prop where
  add : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜),
    Φ (Function.update u j (v + w)) = Φ (Function.update u j v) + Φ (Function.update u j w)
  smul : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (c : 𝕜) (v : Linf 𝕜),
    Φ (Function.update u j (c • v)) = c * Φ (Function.update u j v)
  bound : ∀ u : Fin d → Linf 𝕜, ‖Φ u‖ ≤ C * ∏ j, ‖u j‖

/-! ### Elementary consequences of `IsBddML` -/

namespace IsBddML

variable {d : ℕ} {Φ : (Fin d → Linf 𝕜) → 𝕜} {C : ℝ}

/-- If one of the arguments is zero, the value is zero. -/
theorem eq_zero_of_eq_zero (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d)
    (hj : u j = 0) : Φ u = 0 := by
  have h0 : Φ (Function.update u j ((0 : 𝕜) • u j)) = (0 : 𝕜) * Φ (Function.update u j (u j)) :=
    hΦ.smul u j 0 (u j)
  rwa [zero_smul, ← hj, Function.update_eq_self, zero_mul] at h0

/-- Updating a slot by zero gives zero. -/
theorem update_zero (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Φ (Function.update u j 0) = 0 :=
  hΦ.eq_zero_of_eq_zero _ j (Function.update_self _ _ _)

theorem update_sub (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜) :
    Φ (Function.update u j (v - w)) = Φ (Function.update u j v) - Φ (Function.update u j w) := by
  have := hΦ.add u j (v - w) w
  rw [sub_add_cancel] at this
  rw [this]
  ring

theorem update_sum (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) {ι : Type*}
    (s : Finset ι) (f : ι → Linf 𝕜) :
    Φ (Function.update u j (∑ i ∈ s, f i)) = ∑ i ∈ s, Φ (Function.update u j (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hΦ.update_zero u j
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hΦ.add, ih]

end IsBddML

/-! ### The `Fin 4` case -/

theorem isBddML_of_isBdd4 {Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜} {C : ℝ}
    (hΛ : IsBdd4 𝕜 Λ C) :
    IsBddML (fun u : Fin 4 → Linf 𝕜 => Λ (u 0) (u 1) (u 2) (u 3)) C where
  add := by
    intro u j v w
    fin_cases j <;>
      simp [hΛ.add₁, hΛ.add₂, hΛ.add₃, hΛ.add₄]
  smul := by
    intro u j c v
    fin_cases j <;>
      simp [hΛ.smul₁, hΛ.smul₂, hΛ.smul₃, hΛ.smul₄]
  bound := by
    intro u
    simpa [Fin.prod_univ_four, mul_assoc] using hΛ.bound (u 0) (u 1) (u 2) (u 3)

/-! ### Truncations in `ℓ^∞` -/

theorem Linf.add_apply (f g : Linf 𝕜) (k : ℕ) : (f + g) k = f k + g k := rfl

theorem Linf.sum_apply {ι : Type*} (s : Finset ι) (f : ι → Linf 𝕜) (k : ℕ) :
    (∑ i ∈ s, f i) k = ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- `headOf M x` keeps the coordinates `< M` of `x` and kills the others. -/
noncomputable def headOf (M : ℕ) (x : Linf 𝕜) : Linf 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if i < M then x i else 0) ‖x‖ (by
      intro i
      split_ifs
      · exact x.norm_coe_le_norm i
      · simpa using norm_nonneg x)

@[simp] theorem headOf_apply (M : ℕ) (x : Linf 𝕜) (i : ℕ) :
    headOf M x i = if i < M then x i else 0 := rfl

/-- `tailOf M x` kills the coordinates `< M` of `x` and keeps the others. -/
noncomputable def tailOf (M : ℕ) (x : Linf 𝕜) : Linf 𝕜 := x - headOf M x

theorem tailOf_apply (M : ℕ) (x : Linf 𝕜) (i : ℕ) :
    tailOf M x i = if i < M then 0 else x i := by
  show x i - (if i < M then x i else 0) = _
  split_ifs <;> simp

theorem tailOf_apply_of_lt {M : ℕ} (x : Linf 𝕜) {i : ℕ} (hi : i < M) : tailOf M x i = 0 := by
  simp [tailOf_apply, hi]

theorem headOf_add_tailOf (M : ℕ) (x : Linf 𝕜) : headOf M x + tailOf M x = x := by
  simp [tailOf]

theorem norm_headOf_le (M : ℕ) (x : Linf 𝕜) : ‖headOf M x‖ ≤ ‖x‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg x)]
  intro i
  rw [headOf_apply]
  split_ifs
  · exact x.norm_coe_le_norm i
  · simpa using norm_nonneg x

theorem norm_tailOf_le (M : ℕ) (x : Linf 𝕜) : ‖tailOf M x‖ ≤ ‖x‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg x)]
  intro i
  rw [tailOf_apply]
  split_ifs
  · simpa using norm_nonneg x
  · exact x.norm_coe_le_norm i

/-- If `x` already vanishes below `M`, truncating changes nothing. -/
theorem tailOf_eq_self {M : ℕ} {x : Linf 𝕜} (h : ∀ i < M, x i = 0) : tailOf M x = x := by
  ext i
  rw [tailOf_apply]
  split_ifs with hi
  · exact (h i hi).symm
  · rfl

/-! ### Unit vectors -/

theorem headOf_eq_sum (M : ℕ) (x : Linf 𝕜) :
    headOf M x = ∑ i ∈ Finset.range M, x i • basisVec 𝕜 i := by
  ext k
  rw [headOf_apply, Linf.sum_apply]
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
    · rw [basisVec_apply_self, mul_one]
    · intro b _ hb
      rw [basisVec_apply_ne (Ne.symm hb), mul_zero]
  · symm
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hb' : b < M := Finset.mem_range.mp hb
    rw [basisVec_apply_ne (show k ≠ b by omega), mul_zero]

/-! ### Freezing a slot, and the functional in one slot -/

/-- Freeze the `j`-th slot of a `(d+1)`-linear form at `v`, obtaining a `d`-linear form. -/
def freezeSlot {d : ℕ} (Φ : (Fin (d + 1) → Linf 𝕜) → 𝕜) (j : Fin (d + 1)) (v : Linf 𝕜) :
    (Fin d → Linf 𝕜) → 𝕜 := fun u => Φ (j.insertNth v u)

theorem IsBddML.freezeSlot {d : ℕ} {Φ : (Fin (d + 1) → Linf 𝕜) → 𝕜} {C : ℝ} (hΦ : IsBddML Φ C)
    (j : Fin (d + 1)) (v : Linf 𝕜) : IsBddML (AltCounter.freezeSlot Φ j v) (C * ‖v‖) where
  add := by
    intro u k a b
    simp only [AltCounter.freezeSlot, Fin.insertNth_update]
    exact hΦ.add _ _ a b
  smul := by
    intro u k c a
    simp only [AltCounter.freezeSlot, Fin.insertNth_update]
    exact hΦ.smul _ _ c a
  bound := by
    intro u
    refine (hΦ.bound (j.insertNth v u)).trans_eq ?_
    rw [Fin.prod_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring

variable {d : ℕ} {Φ : (Fin d → Linf 𝕜) → 𝕜} {C : ℝ}

/-- The linear map obtained by letting the `j`-th slot vary. -/
noncomputable def slotMap (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Linf 𝕜 →ₗ[𝕜] 𝕜 where
  toFun v := Φ (Function.update u j v)
  map_add' := hΦ.add u j
  map_smul' := by intro c v; simpa using hΦ.smul u j c v

theorem slotMap_bound (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v : Linf 𝕜) :
    ‖slotMap hΦ u j v‖ ≤ (C * ∏ i ∈ Finset.univ \ {j}, ‖u i‖) * ‖v‖ := by
  classical
  refine (hΦ.bound (Function.update u j v)).trans_eq ?_
  have hfun : (fun i => ‖(Function.update u j v) i‖)
      = Function.update (fun i => ‖u i‖) j ‖v‖ := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Function.update_of_ne hij]
  rw [show (∏ i, ‖(Function.update u j v) i‖) = ∏ i, Function.update (fun i => ‖u i‖) j ‖v‖ i by
        rw [hfun]]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

/-- The continuous linear functional obtained by letting the `j`-th slot vary. -/
noncomputable def slotCLM (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Linf 𝕜 →L[𝕜] 𝕜 :=
  (slotMap hΦ u j).mkContinuous (C * ∏ i ∈ Finset.univ \ {j}, ‖u i‖) (slotMap_bound hΦ u j)

@[simp] theorem slotCLM_apply (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v : Linf 𝕜) :
    slotCLM hΦ u j v = Φ (Function.update u j v) := rfl

/-- Updating a slot is the same as inserting into the tuple with that slot removed. -/
theorem update_eq_insertNth {D : ℕ} (u : Fin (D + 1) → Linf 𝕜) (j : Fin (D + 1)) (v : Linf 𝕜) :
    Function.update u j v = j.insertNth v (fun l => u (j.succAbove l)) := by
  funext m
  induction m using j.succAboveCases with
  | x => simp
  | p l =>
      rw [Function.update_of_ne (Fin.succAbove_ne j l), Fin.insertNth_apply_succAbove]

variable (𝕜) in
/-- The conclusion of `tail_multilinear` at a fixed arity. -/
def TailAt (d : ℕ) : Prop :=
  ∀ (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε

theorem tailAt_zero : TailAt 𝕜 0 := by
  intro Φ C hΦ ε hε
  refine ⟨0, ?_⟩
  rintro u - ⟨j, -⟩
  exact j.elim0

variable [IsUltrametricDist 𝕜] [CompleteSpace 𝕜]

theorem tailAt_one (h : NSC 𝕜) : TailAt 𝕜 1 := by
  intro Φ C hΦ ε hε
  obtain ⟨N, hN⟩ := tail_functional h (slotCLM hΦ (fun _ => 0) 0) ε hε
  refine ⟨N, ?_⟩
  rintro u hu ⟨j, hj⟩
  have hj0 : j = 0 := Subsingleton.elim _ _
  subst hj0
  have hueq : u = Function.update (fun _ => (0 : Linf 𝕜)) 0 (u 0) := by
    funext m
    have hm : m = 0 := Subsingleton.elim _ _
    subst hm
    simp
  rw [hueq]
  simpa using hN (u 0) (hu 0) hj

section Claims

variable {D : ℕ} {Φ : (Fin (D + 1) → Linf 𝕜) → 𝕜} {C ε : ℝ}

/-- **Claim 1.** If the tail property fails with margin `ε`, then it fails with *all* slots
supported arbitrarily far out. -/
theorem claim_all_slots (hΦ : IsBddML Φ C) (hε : 0 < ε) (ih : TailAt 𝕜 D)
    (hF : ∀ N : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧
      (∃ j, ∀ i < N, u j i = 0) ∧ ε < ‖Φ u‖) (M : ℕ) :
    ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧ (∀ j, ∀ i < M, u j i = 0) ∧ ε < ‖Φ u‖ := by
  classical
  -- thresholds for the forms obtained by freezing one slot at a unit vector
  have hTh0 : ∀ (j : Fin (D + 1)) (i : ℕ), ∃ N : ℕ, ∀ w : Fin D → Linf 𝕜, (∀ l, ‖w l‖ ≤ 1) →
      (∃ l, ∀ t < N, w l t = 0) → ‖freezeSlot Φ j (basisVec 𝕜 i) w‖ ≤ ε :=
    fun j i => ih _ _ (hΦ.freezeSlot j (basisVec 𝕜 i)) ε hε
  choose Th hTh using hTh0
  have R : ∀ k : ℕ, ∀ M N : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j : Fin (D + 1), (j : ℕ) < k → ∀ i < M, u j i = 0) ∧
      (∃ j, ∀ i < N, u j i = 0) ∧ ε < ‖Φ u‖ := by
    intro k
    induction k with
    | zero =>
        intro M N
        obtain ⟨u, h1, h2, h3⟩ := hF N
        exact ⟨u, h1, fun j hj => absurd hj (Nat.not_lt_zero _), h2, h3⟩
    | succ k ihk =>
        intro M N
        by_cases hk : k < D + 1
        · obtain ⟨jk, hjk⟩ : ∃ jk : Fin (D + 1), (jk : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
          obtain ⟨N', hN'N, hN'M, hN'T⟩ :
              ∃ N' : ℕ, N ≤ N' ∧ M ≤ N' ∧ ∀ i < M, Th jk i ≤ N' := by
            refine ⟨max (max N M) ((Finset.range M).sup (Th jk)), ?_, ?_, ?_⟩
            · exact le_trans (le_max_left N M) (le_max_left _ _)
            · exact le_trans (le_max_right N M) (le_max_left _ _)
            · intro i hi
              exact le_trans (Finset.le_sup (Finset.mem_range.mpr hi)) (le_max_right _ _)
          obtain ⟨u, hu1, hu2, ⟨j0, hj0⟩, hu4⟩ := ihk M N'
          have hsplit : Φ u = Φ (Function.update u jk (headOf M (u jk)))
              + Φ (Function.update u jk (tailOf M (u jk))) := by
            have hadd := hΦ.add u jk (headOf M (u jk)) (tailOf M (u jk))
            rwa [headOf_add_tailOf, Function.update_eq_self] at hadd
          by_cases hcase : ε < ‖Φ (Function.update u jk (tailOf M (u jk)))‖
          · refine ⟨Function.update u jk (tailOf M (u jk)), ?_, ?_, ?_, hcase⟩
            · intro j
              by_cases hj : j = jk
              · subst hj
                rw [Function.update_self]
                exact (norm_tailOf_le _ _).trans (hu1 j)
              · rw [Function.update_of_ne hj]; exact hu1 j
            · intro j hj i hi
              by_cases hjkj : j = jk
              · subst hjkj
                rw [Function.update_self]
                exact tailOf_apply_of_lt _ hi
              · rw [Function.update_of_ne hjkj]
                refine hu2 j ?_ i hi
                have hne : (j : ℕ) ≠ k := fun hc => hjkj (Fin.val_injective (hc.trans hjk.symm))
                omega
            · by_cases hj0k : j0 = jk
              · refine ⟨jk, fun i hi => ?_⟩
                rw [Function.update_self, tailOf_apply]
                split_ifs with h1
                · rfl
                · rw [← hj0k]
                  exact hj0 i (by omega)
              · refine ⟨j0, fun i hi => ?_⟩
                rw [Function.update_of_ne hj0k]
                exact hj0 i (by omega)
          · exfalso
            push_neg at hcase
            have hA : ε < ‖Φ (Function.update u jk (headOf M (u jk)))‖ := by
              by_contra hcon
              push_neg at hcon
              have hmax := IsUltrametricDist.norm_add_le_max
                (Φ (Function.update u jk (headOf M (u jk))))
                (Φ (Function.update u jk (tailOf M (u jk))))
              rw [← hsplit] at hmax
              have : ‖Φ u‖ ≤ ε := hmax.trans (max_le hcon hcase)
              linarith
            have hAsum : Φ (Function.update u jk (headOf M (u jk)))
                = ∑ i ∈ Finset.range M, (u jk i) * Φ (Function.update u jk (basisVec 𝕜 i)) := by
              rw [headOf_eq_sum, hΦ.update_sum]
              exact Finset.sum_congr rfl fun i _ => hΦ.smul u jk (u jk i) (basisVec 𝕜 i)
            rw [hAsum] at hA
            have hMpos : 0 < M := by
              rcases Nat.eq_zero_or_pos M with rfl | hM
              · rw [Finset.range_zero, Finset.sum_empty, norm_zero] at hA; linarith
              · exact hM
            obtain ⟨i0, hi0mem, hi0⟩ :=
              IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
                ⟨0, Finset.mem_range.mpr hMpos⟩
                (fun i => (u jk i) * Φ (Function.update u jk (basisVec 𝕜 i)))
            have hi0M : i0 < M := Finset.mem_range.mp hi0mem
            have hfi0 : ε < ‖(u jk i0) * Φ (Function.update u jk (basisVec 𝕜 i0))‖ :=
              lt_of_lt_of_le hA hi0
            have hu0 : u jk i0 ≠ 0 := by
              intro hz
              rw [hz, zero_mul, norm_zero] at hfi0
              linarith
            have hj0ne : j0 ≠ jk := by
              intro hc
              exact hu0 (hc ▸ hj0 i0 (by omega))
            have hnorm : ε < ‖Φ (Function.update u jk (basisVec 𝕜 i0))‖ := by
              refine lt_of_lt_of_le hfi0 ?_
              rw [norm_mul]
              exact mul_le_of_le_one_left (norm_nonneg _)
                (((u jk).norm_coe_le_norm i0).trans (hu1 jk))
            obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hj0ne
            have hw : Φ (Function.update u jk (basisVec 𝕜 i0))
                = freezeSlot Φ jk (basisVec 𝕜 i0) (fun l => u (jk.succAbove l)) := by
              rw [update_eq_insertNth]; rfl
            have hle := hTh jk i0 (fun l => u (jk.succAbove l)) (fun l => hu1 _)
              ⟨l0, fun t ht => by rw [hl0]; exact hj0 t (by have := hN'T i0 hi0M; omega)⟩
            rw [hw] at hnorm
            linarith
        · obtain ⟨u, hu1, hu2, hu3, hu4⟩ := ihk M N
          refine ⟨u, hu1, ?_, hu3, hu4⟩
          intro j hj i hi
          have hjlt := j.isLt
          exact hu2 j (by omega) i hi
  obtain ⟨u, hu1, hu2, -, hu4⟩ := R (D + 1) M M
  exact ⟨u, hu1, fun j i hi => hu2 j j.isLt i hi, hu4⟩

/-- **Claim 2.** One may moreover take all the slots supported in a finite window `[M, M')`. -/
theorem claim_window (h : NSC 𝕜) (hΦ : IsBddML Φ C) (hε : 0 < ε)
    (hc1 : ∀ M : ℕ, ∃ u : Fin (D + 1) → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) ∧ (∀ j, ∀ i < M, u j i = 0) ∧
      ε < ‖Φ u‖) (M : ℕ) :
    ∃ (M' : ℕ) (u : Fin (D + 1) → Linf 𝕜), M < M' ∧ (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j, ∀ i < M, u j i = 0) ∧ (∀ j, ∀ i, M' ≤ i → u j i = 0) ∧ ε < ‖Φ u‖ := by
  classical
  have S : ∀ k : ℕ, ∃ (M' : ℕ) (u : Fin (D + 1) → Linf 𝕜), M < M' ∧ (∀ j, ‖u j‖ ≤ 1) ∧
      (∀ j, ∀ i < M, u j i = 0) ∧
      (∀ j : Fin (D + 1), (j : ℕ) < k → ∀ i, M' ≤ i → u j i = 0) ∧ ε < ‖Φ u‖ := by
    intro k
    induction k with
    | zero =>
        obtain ⟨u, h1, h2, h3⟩ := hc1 M
        exact ⟨M + 1, u, by omega, h1, h2, fun j hj => absurd hj (Nat.not_lt_zero _), h3⟩
    | succ k ihk =>
        obtain ⟨M', u, hMM', hu1, hu2, hu3, hu4⟩ := ihk
        by_cases hk : k < D + 1
        · obtain ⟨jk, hjk⟩ : ∃ jk : Fin (D + 1), (jk : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
          obtain ⟨N0, hN0⟩ := tail_functional h (slotCLM hΦ u jk) ε hε
          have hMax : M' ≤ max M' N0 := le_max_left _ _
          have hMax' : N0 ≤ max M' N0 := le_max_right _ _
          have hsplit : Φ u = Φ (Function.update u jk (headOf (max M' N0) (u jk)))
              + Φ (Function.update u jk (tailOf (max M' N0) (u jk))) := by
            have hadd := hΦ.add u jk (headOf (max M' N0) (u jk)) (tailOf (max M' N0) (u jk))
            rwa [headOf_add_tailOf, Function.update_eq_self] at hadd
          have htail : ‖Φ (Function.update u jk (tailOf (max M' N0) (u jk)))‖ ≤ ε := by
            refine hN0 (tailOf (max M' N0) (u jk)) ((norm_tailOf_le _ _).trans (hu1 jk)) ?_
            intro i hi
            exact tailOf_apply_of_lt _ (by omega)
          refine ⟨max M' N0, Function.update u jk (headOf (max M' N0) (u jk)), by omega, ?_, ?_,
            ?_, ?_⟩
          · intro j
            by_cases hj : j = jk
            · subst hj
              rw [Function.update_self]
              exact (norm_headOf_le _ _).trans (hu1 j)
            · rw [Function.update_of_ne hj]; exact hu1 j
          · intro j i hi
            by_cases hj : j = jk
            · subst hj
              rw [Function.update_self, headOf_apply]
              split_ifs
              · exact hu2 j i hi
              · rfl
            · rw [Function.update_of_ne hj]; exact hu2 j i hi
          · intro j hj i hi
            by_cases hjkj : j = jk
            · subst hjkj
              rw [Function.update_self, headOf_apply]
              split_ifs with hc
              · exact absurd hc (by omega)
              · rfl
            · rw [Function.update_of_ne hjkj]
              have hne : (j : ℕ) ≠ k := fun hc => hjkj (Fin.val_injective (hc.trans hjk.symm))
              exact hu3 j (by omega) i (by omega)
          · by_contra hcon
            push_neg at hcon
            have hmax := IsUltrametricDist.norm_add_le_max
              (Φ (Function.update u jk (headOf (max M' N0) (u jk))))
              (Φ (Function.update u jk (tailOf (max M' N0) (u jk))))
            rw [← hsplit] at hmax
            have : ‖Φ u‖ ≤ ε := hmax.trans (max_le hcon htail)
            linarith
        · refine ⟨M', u, hMM', hu1, hu2, ?_, hu4⟩
          intro j hj i hi
          have hjlt := j.isLt
          exact hu3 j (by omega) i hi
  obtain ⟨M', u, h1, h2, h3, h4, h5⟩ := S (D + 1)
  exact ⟨M', u, h1, h2, h3, fun j i hi => h4 j j.isLt i hi, h5⟩

end Claims

theorem tailAt_succ (h : NSC 𝕜) {D : ℕ} (hD : 0 < D) (ih : TailAt 𝕜 D) : TailAt 𝕜 (D + 1) := by
  classical
  intro Φ C hΦ ε hε
  by_contra hcon
  push_neg at hcon
  -- Claims 1 and 2: witnesses supported in finite windows
  have hc2 := claim_window h hΦ hε (claim_all_slots hΦ hε ih hcon)
  choose W Z hW hZ1 hZ2 hZ3 hZ4 using hc2
  -- tail thresholds for the forms obtained by freezing slot `0`
  have hT0 : ∀ v : Linf 𝕜, ∃ N : ℕ, ∀ w : Fin D → Linf 𝕜, (∀ l, ‖w l‖ ≤ 1) →
      (∃ l, ∀ t < N, w l t = 0) → ‖freezeSlot Φ 0 v w‖ ≤ ε :=
    fun v => ih _ _ (hΦ.freezeSlot 0 v) ε hε
  choose T hT using hT0
  -- tail thresholds for the functionals in slot `0`
  have hS0 : ∀ u : Fin (D + 1) → Linf 𝕜, ∃ N : ℕ, ∀ y : Linf 𝕜, ‖y‖ ≤ 1 → (∀ i < N, y i = 0) →
      ‖Φ (Function.update u 0 y)‖ ≤ ε := by
    intro u
    obtain ⟨N, hN⟩ := tail_functional h (slotCLM hΦ u 0) ε hε
    exact ⟨N, fun y hy1 hy2 => by simpa using hN y hy1 hy2⟩
  choose Sf hS using hS0
  -- the increasing sequence of window endpoints
  obtain ⟨Mseq, hM0, hMstep⟩ : ∃ Mseq : ℕ → ℕ, Mseq 0 = 0 ∧
      ∀ s, Mseq (s + 1) = max (W (Mseq s)) (max (Sf (Z (Mseq s))) (T (Z (Mseq s) 0))) :=
    ⟨fun s => Nat.rec 0 (fun _ Ms => max (W Ms) (max (Sf (Z Ms)) (T (Z Ms 0)))) s, rfl, fun _ => rfl⟩
  have hWle : ∀ s, W (Mseq s) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_max_left _ _
  have hSle : ∀ s, Sf (Z (Mseq s)) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTle : ∀ s, T (Z (Mseq s) 0) ≤ Mseq (s + 1) := by
    intro s; rw [hMstep]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmono : ∀ s, Mseq s < Mseq (s + 1) := fun s => lt_of_lt_of_le (hW _) (hWle s)
  have hMle : ∀ s t : ℕ, s ≤ t → Mseq s ≤ Mseq t :=
    fun s t hst => monotone_nat_of_le_succ (fun n => (hmono n).le) hst
  have hMge : ∀ s, s ≤ Mseq s := by
    intro s
    induction s with
    | zero => omega
    | succ t iht => have := hmono t; omega
  -- the glued diagonal vector
  obtain ⟨x, hxnorm, hxapp⟩ : ∃ x : Linf 𝕜, ‖x‖ ≤ 1 ∧
      ∀ i, x i = ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i := by
    have hxbd : ∀ i : ℕ, ‖∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i‖ ≤ 1 := by
      intro i
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro r _
      exact ((Z (Mseq r) 0).norm_coe_le_norm i).trans (hZ1 _ _)
    exact ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun i => ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i) 1 hxbd,
      (BoundedContinuousFunction.norm_le zero_le_one).mpr hxbd, fun i => rfl⟩
  -- the coordinates of `x` in the window of index `s`
  have hxwin : ∀ (s i : ℕ), i < Mseq (s + 1) →
      x i = ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i := by
    intro s i hi
    rw [hxapp]
    have h1 : ∑ r ∈ Finset.range (i + 1), (Z (Mseq r) 0) i
        = ∑ r ∈ Finset.range (max (i + 1) (s + 1)), (Z (Mseq r) 0) i := by
      refine Finset.sum_subset (fun r hr => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hr) (le_max_left _ _))) ?_
      intro r _ hr
      rw [Finset.mem_range] at hr
      exact hZ2 _ _ i (by have := hMge r; omega)
    have h2 : ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i
        = ∑ r ∈ Finset.range (max (i + 1) (s + 1)), (Z (Mseq r) 0) i := by
      refine Finset.sum_subset (fun r hr => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hr) (le_max_right _ _))) ?_
      intro r _ hr
      rw [Finset.mem_range] at hr
      exact hZ2 _ _ i (lt_of_lt_of_le hi (hMle _ _ (by omega)))
    rw [h1, ← h2]
  -- the decomposition of `x` adapted to the window of index `s`
  have hdecomp : ∀ s : ℕ, x = (∑ r ∈ Finset.range s, (Z (Mseq r) 0)) + (Z (Mseq s) 0)
      + tailOf (Mseq (s + 1)) x := by
    intro s
    ext i
    rw [Linf.add_apply, Linf.add_apply, Linf.sum_apply, tailOf_apply]
    by_cases hi : i < Mseq (s + 1)
    · rw [if_pos hi, add_zero, ← Finset.sum_range_succ]
      exact hxwin s i hi
    · rw [if_neg hi]
      have hzero : ∀ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i = 0 := by
        intro r hr
        rw [Finset.mem_range] at hr
        refine hZ3 _ _ i ?_
        have h1 : W (Mseq r) ≤ Mseq (r + 1) := hWle r
        have h2 : Mseq (r + 1) ≤ Mseq (s + 1) := hMle _ _ (by omega)
        omega
      have hsum : ∑ r ∈ Finset.range (s + 1), (Z (Mseq r) 0) i = 0 :=
        Finset.sum_eq_zero hzero
      rw [Finset.sum_range_succ] at hsum
      rw [hsum, zero_add]
  -- the "off-diagonal" part is small
  have hP : ∀ s : ℕ,
      ‖Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0)))‖ ≤ ε := by
    intro s
    rw [hΦ.update_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le ?_
    intro r hr
    rw [Finset.mem_range] at hr
    have hw : Φ (Function.update (Z (Mseq s)) 0 (Z (Mseq r) 0))
        = freezeSlot Φ 0 (Z (Mseq r) 0)
          (fun l => Z (Mseq s) ((0 : Fin (D + 1)).succAbove l)) := by
      rw [update_eq_insertNth]; rfl
    rw [hw]
    refine hT (Z (Mseq r) 0) _ (fun l => hZ1 _ _) ⟨⟨0, hD⟩, fun t ht => ?_⟩
    refine hZ2 _ _ t ?_
    have h1 : T (Z (Mseq r) 0) ≤ Mseq (r + 1) := hTle r
    have h2 : Mseq (r + 1) ≤ Mseq s := hMle _ _ (by omega)
    omega
  -- the far tail is small
  have hR : ∀ s : ℕ,
      ‖Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x))‖ ≤ ε := by
    intro s
    refine hS (Z (Mseq s)) _ ((norm_tailOf_le _ _).trans hxnorm) (fun i hi => ?_)
    exact tailOf_apply_of_lt _ (by have := hSle s; omega)
  -- hence the diagonal values stay big
  have hbig : ∀ s : ℕ, ε < ‖Φ (Function.update (Z (Mseq s)) 0 x)‖ := by
    intro s
    by_contra hcon2
    push_neg at hcon2
    have hsplit : Φ (Function.update (Z (Mseq s)) 0 x)
        = Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0)))
          + Φ (Z (Mseq s))
          + Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x)) := by
      conv_lhs => rw [hdecomp s]
      rw [hΦ.add, hΦ.add, Function.update_eq_self]
    have hQ : Φ (Z (Mseq s))
        = Φ (Function.update (Z (Mseq s)) 0 x)
          + (-(Φ (Function.update (Z (Mseq s)) 0 (∑ r ∈ Finset.range s, (Z (Mseq r) 0))))
             + -(Φ (Function.update (Z (Mseq s)) 0 (tailOf (Mseq (s + 1)) x)))) := by
      rw [hsplit]; ring
    have hle : ‖Φ (Z (Mseq s))‖ ≤ ε := by
      rw [hQ]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcon2 ?_)
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
      exact max_le (hP s) (hR s)
    have := hZ4 (Mseq s)
    linarith
  -- but freezing slot `0` at `x` gives a form of smaller arity, whose tail bound applies
  obtain ⟨Nx, hNx⟩ := ih _ _ (hΦ.freezeSlot 0 x) ε hε
  have hxfr : Φ (Function.update (Z (Mseq Nx)) 0 x)
      = freezeSlot Φ 0 x (fun l => Z (Mseq Nx) ((0 : Fin (D + 1)).succAbove l)) := by
    rw [update_eq_insertNth]; rfl
  have hfin := hNx (fun l => Z (Mseq Nx) ((0 : Fin (D + 1)).succAbove l)) (fun l => hZ1 _ _)
    ⟨⟨0, hD⟩, fun t ht => hZ2 _ _ t (by have := hMge Nx; omega)⟩
  have hbg := hbig Nx
  rw [hxfr] at hbg
  linarith

/-- Tails of bounded multilinear forms of any arity. -/
theorem tail_multilinear (h : NSC 𝕜) : ∀ (d : ℕ) (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε := by
  have key : ∀ d : ℕ, TailAt 𝕜 d := by
    intro d
    induction d with
    | zero => exact tailAt_zero
    | succ D ihD =>
        rcases Nat.eq_zero_or_pos D with rfl | hD
        · exact tailAt_one h
        · exact tailAt_succ h hD ihD
  exact fun d => key d

/-- The Phillips property used in the main theorem. -/
theorem tailProperty_of_NSC (h : NSC 𝕜) : TailProperty 𝕜 := by
  intro Λ C hΛ ε hε
  obtain ⟨N, hN⟩ := tail_multilinear h 4 _ C (isBddML_of_isBdd4 hΛ) ε hε
  refine ⟨N, ?_⟩
  intro a b x y ha hb hx hy hdisj
  have hu : ∀ j : Fin 4, ‖(![a, b, x, y] : Fin 4 → Linf 𝕜) j‖ ≤ 1 := by
    intro j; fin_cases j <;> simpa
  have hex : ∃ j : Fin 4, ∀ i < N, (![a, b, x, y] : Fin 4 → Linf 𝕜) j i = 0 := by
    rcases hdisj with h1 | h1 | h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
    · exact ⟨2, by simpa using h1⟩
    · exact ⟨3, by simpa using h1⟩
  simpa using hN _ hu hex

end AltCounter
