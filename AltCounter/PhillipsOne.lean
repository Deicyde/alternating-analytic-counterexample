/-
The multilinear Phillips (tail) property from the classical characterisation of non-spherically-complete
fields: `(ℓ^∞ / c₀)' = 0`, i.e. every continuous linear functional on `ℓ^∞` that kills all the unit vectors is `0`
(van der Put 1969, Thm 3.2: this holds iff the field is not spherically complete).
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import AltCounter.FiniteLemma

namespace AltCounter

open BoundedContinuousFunction Filter Topology

section Aux

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- `y ↦ (i ↦ c i * y (σ i))`, as a function `ℓ^∞ → ℓ^∞`. -/
noncomputable def weightedCompFun (c : ℕ → 𝕜) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M)
    (y : Linf 𝕜) : Linf 𝕜 :=
  ofNormedAddCommGroupDiscrete (fun i => c i * y (σ i)) (M * ‖y‖) (fun i => by
    rw [norm_mul]
    exact mul_le_mul (hM i) (y.norm_coe_le_norm _) (norm_nonneg _)
      ((norm_nonneg (c 0)).trans (hM 0)))

lemma weightedCompFun_apply (c : ℕ → 𝕜) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M)
    (y : Linf 𝕜) (i : ℕ) : weightedCompFun c σ M hM y i = c i * y (σ i) := rfl

lemma norm_weightedCompFun_le (c : ℕ → 𝕜) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M)
    (y : Linf 𝕜) : ‖weightedCompFun c σ M hM y‖ ≤ M * ‖y‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (c 0)).trans (hM 0)
  rw [BoundedContinuousFunction.norm_le (mul_nonneg hM0 (norm_nonneg y))]
  intro i
  rw [weightedCompFun_apply, norm_mul]
  exact mul_le_mul (hM i) (y.norm_coe_le_norm _) (norm_nonneg _) hM0

/-- `y ↦ (i ↦ c i * y (σ i))`, as a bounded operator on `ℓ^∞` of norm at most `M`. -/
noncomputable def weightedComp (c : ℕ → 𝕜) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M) :
    Linf 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous
    { toFun := weightedCompFun c σ M hM
      map_add' := by
        intro y z
        refine BoundedContinuousFunction.ext fun i => ?_
        simp only [weightedCompFun_apply, BoundedContinuousFunction.add_apply, mul_add]
      map_smul' := by
        intro a y
        refine BoundedContinuousFunction.ext fun i => ?_
        simp only [weightedCompFun_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
    M (norm_weightedCompFun_le c σ M hM)

lemma weightedComp_apply (c : ℕ → 𝕜) (σ : ℕ → ℕ) (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M)
    (y : Linf 𝕜) (i : ℕ) : weightedComp c σ M hM y i = c i * y (σ i) := rfl

/-- Truncation: `tailCLM N x` agrees with `x` from `N` on, and vanishes below `N`. -/
noncomputable def tailCLM (N : ℕ) : Linf 𝕜 →L[𝕜] Linf 𝕜 :=
  weightedComp (fun i => if i < N then (0 : 𝕜) else 1) (fun i => i) 1
    (fun i => by split_ifs <;> simp)

lemma tailCLM_apply (N : ℕ) (x : Linf 𝕜) (i : ℕ) :
    tailCLM N x i = if i < N then 0 else x i := by
  simp only [tailCLM, weightedComp_apply]
  split_ifs <;> simp

lemma norm_tailCLM_le (N : ℕ) (x : Linf 𝕜) : ‖tailCLM N x‖ ≤ ‖x‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg x)]
  intro i
  rw [tailCLM_apply]
  split_ifs
  · simp
  · exact x.norm_coe_le_norm i

variable [IsUltrametricDist 𝕜]

/-- In an ultrametric space a sequence whose consecutive differences tend to `0` is Cauchy. -/
theorem cauchySeq_of_tendsto_sub_succ {a : ℕ → 𝕜}
    (h : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0)) : CauchySeq a := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, ?_⟩
  have key : ∀ d n, N ≤ n → dist (a (n + d)) (a n) < ε := by
    intro d
    induction d with
    | zero => intro n _; simpa using hε
    | succ d ih =>
      intro n hn
      have h1 : dist (a (n + d + 1)) (a (n + d)) < ε := by
        have := hN (n + d) (by omega)
        simpa [dist_eq_norm] using this
      have h2 : dist (a (n + d)) (a n) < ε := ih n hn
      have h3 : dist (a (n + d + 1)) (a n) ≤
          max (dist (a (n + d + 1)) (a (n + d))) (dist (a (n + d)) (a n)) :=
        dist_triangle_max _ _ _
      have h4 : n + (d + 1) = n + d + 1 := by omega
      rw [h4]
      exact lt_of_le_of_lt h3 (max_lt h1 h2)
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact key d N le_rfl

end Aux

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- The `i`-th unit vector of `ℓ^∞`. -/
noncomputable def basisVec (i : ℕ) : Linf 𝕜 := blockVec i (fun _ : Fin 1 => (1 : 𝕜))

/-- `(ℓ^∞ / c₀)' = 0`: a continuous linear functional on `ℓ^∞` vanishing on all unit vectors is zero.
For a complete non-archimedean field this is equivalent to: the field is not spherically complete. -/
def NSC : Prop := ∀ φ : Linf 𝕜 →L[𝕜] 𝕜, (∀ i, φ (basisVec 𝕜 i) = 0) → φ = 0

variable {𝕜}

lemma basisVec_apply_self (i : ℕ) : basisVec 𝕜 i i = (1 : 𝕜) := by
  have := blockVec_apply_block (𝕜 := 𝕜) i (fun _ : Fin 1 => (1 : 𝕜)) 0
  simpa [basisVec] using this

lemma basisVec_apply_ne {i j : ℕ} (hij : j ≠ i) : basisVec 𝕜 i j = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact blockVec_apply_of_lt i _ j hlt
  · exact blockVec_apply_of_ge i _ j (by omega)

lemma basisVec_apply (i j : ℕ) : basisVec 𝕜 i j = if j = i then 1 else 0 := by
  split_ifs with hij
  · subst hij; exact basisVec_apply_self _
  · exact basisVec_apply_ne hij

lemma norm_basisVec_le (i : ℕ) : ‖basisVec 𝕜 i‖ ≤ 1 :=
  norm_blockVec_le i _ (fun _ => by simp)

lemma tailCLM_basisVec {N i : ℕ} (hi : i < N) : tailCLM N (basisVec 𝕜 i) = 0 := by
  refine BoundedContinuousFunction.ext fun j => ?_
  rw [tailCLM_apply]
  split_ifs with hj
  · rfl
  · rw [basisVec_apply_ne (by omega)]; rfl

variable [IsUltrametricDist 𝕜] [CompleteSpace 𝕜]

/-- Shift trick: under `NSC`, the values of a functional on the unit vectors tend to `0`. -/
theorem tendsto_apply_basisVec (h : NSC 𝕜) (φ : Linf 𝕜 →L[𝕜] 𝕜) :
    Tendsto (fun i => φ (basisVec 𝕜 i)) atTop (𝓝 0) := by
  classical
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop, ε ≤ ‖φ (basisVec 𝕜 n)‖ := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hn'⟩ := hfreq N
    exact ⟨n, hn, by simpa [dist_zero_right] using hn'⟩
  obtain ⟨k, hk, hkε⟩ := Filter.extraction_of_frequently_atTop hfr
  have hkinj : Function.Injective k := hk.injective
  have hne : ∀ n, φ (basisVec 𝕜 (k n)) ≠ 0 := by
    intro n hn
    have h1 := hkε n
    rw [hn, norm_zero] at h1
    linarith
  -- the "spreading" operator `J`
  have hcb : ∀ i : ℕ,
      ‖(if k (Function.invFun k i) = i then (φ (basisVec 𝕜 i))⁻¹ else 0 : 𝕜)‖ ≤ ε⁻¹ := by
    intro i
    split_ifs with hi
    · rw [norm_inv]
      refine inv_anti₀ hε ?_
      have h1 := hkε (Function.invFun k i)
      rwa [hi] at h1
    · simpa using (inv_pos.mpr hε).le
  set J : Linf 𝕜 →L[𝕜] Linf 𝕜 :=
    weightedComp (fun i => if k (Function.invFun k i) = i then (φ (basisVec 𝕜 i))⁻¹ else 0)
      (Function.invFun k) ε⁻¹ hcb with hJdef
  have hJapp : ∀ (y : Linf 𝕜) (i : ℕ), J y i =
      (if k (Function.invFun k i) = i then (φ (basisVec 𝕜 i))⁻¹ else 0) * y (Function.invFun k i) :=
    fun y i => rfl
  have hJb : ∀ n, J (basisVec 𝕜 n) = (φ (basisVec 𝕜 (k n)))⁻¹ • basisVec 𝕜 (k n) := by
    intro n
    refine BoundedContinuousFunction.ext fun i => ?_
    rw [hJapp, BoundedContinuousFunction.smul_apply, smul_eq_mul]
    split_ifs with hi
    · rw [← hi, Function.leftInverse_invFun hkinj]
      by_cases hm : Function.invFun k i = n
      · rw [hm, basisVec_apply_self, basisVec_apply_self]
      · rw [basisVec_apply_ne hm, basisVec_apply_ne (fun hh => hm (hkinj hh)),
          mul_zero, mul_zero]
    · have hne2 : i ≠ k n := by
        intro hh
        exact hi (by rw [hh, Function.leftInverse_invFun hkinj])
      rw [zero_mul, basisVec_apply_ne hne2, mul_zero]
  -- the functional `ψ` takes the value `1` on every unit vector
  set ψ : Linf 𝕜 →L[𝕜] 𝕜 := φ.comp J with hψdef
  have hψ : ∀ n, ψ (basisVec 𝕜 n) = 1 := by
    intro n
    have : ψ (basisVec 𝕜 n) = φ (J (basisVec 𝕜 n)) := rfl
    rw [this, hJb n, map_smul, smul_eq_mul, inv_mul_cancel₀ (hne n)]
  -- the right shift
  have hSb : ∀ i : ℕ, ‖(if i = 0 then (0 : 𝕜) else 1)‖ ≤ 1 := by
    intro i; split_ifs <;> simp
  set S : Linf 𝕜 →L[𝕜] Linf 𝕜 :=
    weightedComp (fun i => if i = 0 then (0 : 𝕜) else 1) (fun i => i - 1) 1 hSb with hSdef
  have hSapp : ∀ (y : Linf 𝕜) (i : ℕ), S y i = (if i = 0 then (0 : 𝕜) else 1) * y (i - 1) :=
    fun y i => rfl
  have hSbasis : ∀ n, S (basisVec 𝕜 n) = basisVec 𝕜 (n + 1) := by
    intro n
    refine BoundedContinuousFunction.ext fun i => ?_
    rw [hSapp]
    rcases i with _ | j
    · simp [basisVec_apply]
    · simp [basisVec_apply]
  -- the constant sequence
  set e : Linf 𝕜 := BoundedContinuousFunction.const ℕ (1 : 𝕜) with hedef
  have heS : e - S e = basisVec 𝕜 0 := by
    refine BoundedContinuousFunction.ext fun i => ?_
    rw [BoundedContinuousFunction.sub_apply, hSapp]
    rcases i with _ | j
    · simp [hedef, basisVec_apply]
    · simp [hedef, basisVec_apply]
  -- `χ` kills every unit vector, hence is `0`, yet `χ e = 1`
  set χ : Linf 𝕜 →L[𝕜] 𝕜 := ψ - ψ.comp S with hχdef
  have hχ : ∀ n, χ (basisVec 𝕜 n) = 0 := by
    intro n
    have h1 : χ (basisVec 𝕜 n) = ψ (basisVec 𝕜 n) - ψ (S (basisVec 𝕜 n)) := rfl
    rw [h1, hSbasis, hψ, hψ, sub_self]
  have hχ0 : χ = 0 := h χ hχ
  have h1 : χ e = 0 := by rw [hχ0]; rfl
  have h2 : χ e = ψ (e - S e) := by
    have : χ e = ψ e - ψ (S e) := rfl
    rw [this, ← map_sub]
  rw [h2, heS, hψ 0] at h1
  exact one_ne_zero h1

/-- For each fixed `x`, the values of `φ` on the tails of `x` tend to `0`. -/
theorem tendsto_apply_tail (h : NSC 𝕜) (φ : Linf 𝕜 →L[𝕜] 𝕜) (x : Linf 𝕜) :
    Tendsto (fun N => φ (tailCLM N x)) atTop (𝓝 0) := by
  classical
  -- consecutive differences: `φ (tail (N+1) x) - φ (tail N x) = -(x N * φ (basisVec N))`
  have hdiff : ∀ (z : Linf 𝕜) (N : ℕ),
      tailCLM N z - tailCLM (N + 1) z = z N • basisVec 𝕜 N := by
    intro z N
    refine BoundedContinuousFunction.ext fun i => ?_
    rw [BoundedContinuousFunction.sub_apply, tailCLM_apply, tailCLM_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, basisVec_apply]
    rcases lt_trichotomy i N with h1 | h1 | h1
    · simp [h1, show i < N + 1 by omega, show ¬ (i = N) by omega]
    · simp [h1]
    · simp [show ¬ (i < N) by omega, show ¬ (i < N + 1) by omega, show ¬ (i = N) by omega]
  have hbas : Tendsto (fun i => φ (basisVec 𝕜 i)) atTop (𝓝 0) := tendsto_apply_basisVec h φ
  have hconv : ∀ z : Linf 𝕜, ∃ L : 𝕜, Tendsto (fun N => φ (tailCLM N z)) atTop (𝓝 L) := by
    intro z
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_tendsto_sub_succ ?_)
    have hfun : ∀ N : ℕ, φ (tailCLM (N + 1) z) - φ (tailCLM N z)
        = -(z N * φ (basisVec 𝕜 N)) := by
      intro N
      have h1 : φ (tailCLM N z) - φ (tailCLM (N + 1) z) = z N * φ (basisVec 𝕜 N) := by
        rw [← map_sub, hdiff z N, map_smul, smul_eq_mul]
      rw [← neg_sub, h1]
    refine squeeze_zero_norm (a := fun N => ‖z‖ * ‖φ (basisVec 𝕜 N)‖) (fun N => ?_) ?_
    · rw [hfun N, norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right (z.norm_coe_le_norm N) (norm_nonneg _)
    · have h6 := hbas.norm
      rw [norm_zero] at h6
      simpa using h6.const_mul ‖z‖
  choose L hL using hconv
  have hLadd : ∀ y z : Linf 𝕜, L (y + z) = L y + L z := by
    intro y z
    refine tendsto_nhds_unique (hL (y + z)) ?_
    have hfun : (fun N => φ (tailCLM N (y + z)))
        = fun N => φ (tailCLM N y) + φ (tailCLM N z) := by
      funext N; rw [map_add, map_add]
    rw [hfun]
    exact (hL y).add (hL z)
  have hLsmul : ∀ (a : 𝕜) (z : Linf 𝕜), L (a • z) = a * L z := by
    intro a z
    refine tendsto_nhds_unique (hL (a • z)) ?_
    have hfun : (fun N => φ (tailCLM N (a • z))) = fun N => a * φ (tailCLM N z) := by
      funext N; rw [map_smul, map_smul, smul_eq_mul]
    rw [hfun]
    exact (hL z).const_mul a
  have hLb : ∀ z : Linf 𝕜, ‖L z‖ ≤ ‖φ‖ * ‖z‖ := by
    intro z
    refine le_of_tendsto ((hL z).norm) (Eventually.of_forall fun N => ?_)
    refine (φ.le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_tailCLM_le N z) (norm_nonneg φ)
  set ψ : Linf 𝕜 →L[𝕜] 𝕜 :=
    LinearMap.mkContinuous
      { toFun := L
        map_add' := hLadd
        map_smul' := fun a z => by simpa using hLsmul a z } ‖φ‖ hLb with hψdef
  have hψapp : ∀ z : Linf 𝕜, ψ z = L z := fun z => rfl
  have hψbas : ∀ i, ψ (basisVec 𝕜 i) = 0 := by
    intro i
    rw [hψapp]
    refine tendsto_nhds_unique (hL (basisVec 𝕜 i)) ?_
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : 𝕜)) (f := atTop))
    filter_upwards [eventually_gt_atTop i] with N hN
    rw [tailCLM_basisVec hN, map_zero]
  have hψ0 : ψ = 0 := h ψ hψbas
  have : L x = 0 := by
    have h1 : ψ x = 0 := by rw [hψ0]; rfl
    rwa [hψapp] at h1
  have := hL x
  rwa [‹L x = 0›] at this

/-- Tails of a functional: uniform smallness on unit vectors supported far out. -/
theorem tail_functional (h : NSC 𝕜) (φ : Linf 𝕜 →L[𝕜] 𝕜) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : Linf 𝕜, ‖x‖ ≤ 1 → (∀ i < N, x i = 0) → ‖φ x‖ ≤ ε := by
  classical
  by_contra hcon
  push_neg at hcon
  -- gliding hump: a step producing a unit window far out on which `φ` is large
  have hstep : ∀ N : ℕ, ∃ p : ℕ × Linf 𝕜, N < p.1 ∧ ‖p.2‖ ≤ 1 ∧ (∀ i < N, p.2 i = 0) ∧
      (∀ i, p.1 ≤ i → p.2 i = 0) ∧ ε < ‖φ p.2‖ := by
    intro N
    obtain ⟨x, hx1, hx2, hx3⟩ := hcon N
    obtain ⟨M, hM1, hM2⟩ : ∃ M, N < M ∧ ‖φ (tailCLM M x)‖ ≤ ε := by
      have hT := tendsto_apply_tail h φ x
      rw [Metric.tendsto_atTop] at hT
      obtain ⟨M0, hM0⟩ := hT ε hε
      refine ⟨max M0 (N + 1), by omega, le_of_lt ?_⟩
      have := hM0 (max M0 (N + 1)) (le_max_left _ _)
      simpa [dist_zero_right] using this
    refine ⟨(M, x - tailCLM M x), hM1, ?_, ?_, ?_, ?_⟩
    · rw [BoundedContinuousFunction.norm_le zero_le_one]
      intro i
      rw [BoundedContinuousFunction.sub_apply, tailCLM_apply]
      split_ifs with hiM
      · rw [sub_zero]; exact (x.norm_coe_le_norm i).trans hx1
      · rw [sub_self, norm_zero]; exact zero_le_one
    · intro i hiN
      rw [BoundedContinuousFunction.sub_apply, tailCLM_apply, hx2 i hiN]
      split_ifs <;> simp
    · intro i hiM
      have hnot : ¬ (i < M) := by omega
      rw [BoundedContinuousFunction.sub_apply, tailCLM_apply]
      simp [hnot]
    · by_contra hle
      push_neg at hle
      have hsplit : φ x = φ (x - tailCLM M x) + φ (tailCLM M x) := by
        rw [← map_add]; congr 1; abel
      have h2 : ‖φ x‖ ≤ max ‖φ (x - tailCLM M x)‖ ‖φ (tailCLM M x)‖ := by
        rw [hsplit]; exact IsUltrametricDist.norm_add_le_max _ _
      have h3 : ‖φ x‖ ≤ ε := h2.trans (max_le hle hM2)
      linarith
  choose f hf1 hf2 hf3 hf4 hf5 using hstep
  -- the increasing sequence of window endpoints and the windows themselves
  set nn : ℕ → ℕ := fun k => Nat.recAux 0 (fun _ N => (f N).1) k with hnndef
  have hnn0 : nn 0 = 0 := rfl
  have hnnS : ∀ k, nn (k + 1) = (f (nn k)).1 := fun k => rfl
  have hnnmono : StrictMono nn := strictMono_nat_of_lt_succ (fun k => hf1 (nn k))
  set w : ℕ → Linf 𝕜 := fun k => (f (nn k)).2 with hwdef
  have hw1 : ∀ k, ‖w k‖ ≤ 1 := fun k => hf2 (nn k)
  have hw2 : ∀ k, ∀ i < nn k, w k i = 0 := fun k => hf3 (nn k)
  have hw3 : ∀ k i, nn (k + 1) ≤ i → w k i = 0 := fun k i hi => hf4 (nn k) i hi
  have hw4 : ∀ k, ε < ‖φ (w k)‖ := fun k => hf5 (nn k)
  -- the index of the window containing `i`
  have hex : ∀ i : ℕ, ∃ m, i < nn (m + 1) := by
    intro i
    exact ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) hnnmono.le_apply⟩
  obtain ⟨κ, hκ1, hκ2⟩ :
      ∃ κ : ℕ → ℕ, (∀ i, i < nn (κ i + 1)) ∧ (∀ i, nn (κ i) ≤ i) := by
    refine ⟨fun i => Nat.find (hex i), fun i => Nat.find_spec (hex i), ?_⟩
    intro i
    show nn (Nat.find (hex i)) ≤ i
    rcases Nat.eq_zero_or_pos (Nat.find (hex i)) with h0 | h0
    · rw [h0, hnn0]; exact Nat.zero_le i
    · have hmin : ¬ (i < nn (Nat.find (hex i) - 1 + 1)) :=
        Nat.find_min (hex i) (by omega)
      rw [Nat.sub_add_cancel h0] at hmin
      omega
  -- the operator sending the `k`-th unit vector to the `k`-th window
  have hTb : ∀ i : ℕ, ‖w (κ i) i‖ ≤ 1 := fun i => ((w (κ i)).norm_coe_le_norm i).trans (hw1 _)
  set T : Linf 𝕜 →L[𝕜] Linf 𝕜 := weightedComp (fun i => w (κ i) i) κ 1 hTb with hTdef
  have hTapp : ∀ (y : Linf 𝕜) (i : ℕ), T y i = w (κ i) i * y (κ i) := fun y i => rfl
  have hT : ∀ k, T (basisVec 𝕜 k) = w k := by
    intro k
    refine BoundedContinuousFunction.ext fun i => ?_
    rw [hTapp]
    by_cases hik : κ i = k
    · rw [hik, basisVec_apply_self, mul_one]
    · rw [basisVec_apply_ne hik, mul_zero, eq_comm]
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · exact hw2 k i (lt_of_lt_of_le (hκ1 i) (hnnmono.monotone (by omega)))
      · exact hw3 k i (le_trans (hnnmono.monotone (by omega)) (hκ2 i))
  have hfin := tendsto_apply_basisVec h (φ.comp T)
  rw [Metric.tendsto_atTop] at hfin
  obtain ⟨K, hK⟩ := hfin ε hε
  have hlt := hK K le_rfl
  have hval : (φ.comp T) (basisVec 𝕜 K) = φ (w K) := by
    have : (φ.comp T) (basisVec 𝕜 K) = φ (T (basisVec 𝕜 K)) := rfl
    rw [this, hT]
  rw [hval, dist_zero_right] at hlt
  linarith [hw4 K]

end AltCounter
