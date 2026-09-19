/-
An analytic map which is homogeneous of degree 2 is the diagonal of a continuous bilinear map
(in every characteristic: uniqueness of one-variable power series coefficients).
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.CPolynomialDef

namespace AltCounter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The one-variable formal power series of `t ↦ t ^ 2 • v`: all terms vanish except the one of
degree `2`, which is `t ↦ t ^ 2 • v`. -/
noncomputable def sqSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (v : Z) :
    FormalMultilinearSeries 𝕜 𝕜 Z :=
  fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (if n = 2 then v else 0)

lemma sqSeries_apply (v : Z) (n : ℕ) (m : Fin n → 𝕜) :
    sqSeries 𝕜 v n m = (∏ i, m i) • (if n = 2 then v else 0) :=
  ContinuousMultilinearMap.mkPiRing_apply _ _

lemma sqSeries_eq_zero_of_ne (v : Z) {n : ℕ} (hn : n ≠ 2) : sqSeries 𝕜 v n = 0 := by
  have hv : (if n = 2 then v else 0) = 0 := by simp [hn]
  rw [sqSeries, hv]
  exact ContinuousMultilinearMap.mkPiRing_zero

lemma hasFPowerSeriesAt_sqSeries (v : Z) :
    HasFPowerSeriesAt (fun t : 𝕜 => t ^ 2 • v) (sqSeries 𝕜 v) 0 := by
  have H : HasFiniteFPowerSeriesOnBall (fun t : 𝕜 => t ^ 2 • v) (sqSeries 𝕜 v) 0 3 ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro m hm
      exact sqSeries_eq_zero_of_ne v (by omega)
    · intro y _
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        sqSeries_apply, sqSeries_apply, sqSeries_apply]
      simp
  exact H.hasFiniteFPowerSeriesAt.hasFPowerSeriesAt

theorem exists_bilinear_of_analyticAt_of_homogeneous (Q : X → Z)
    (hQ : ∀ (c : 𝕜) (f : X), Q (c • f) = c ^ 2 • Q f) (h : AnalyticAt 𝕜 Q 0) :
    ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => X) Z, ∀ f, P (fun _ => f) = Q f := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p 2, fun y => ?_⟩
  obtain ⟨u, huapp⟩ : ∃ u : 𝕜 →L[𝕜] X, ∀ t : 𝕜, u t = t • y :=
    ⟨(ContinuousLinearMap.id 𝕜 𝕜).smulRight y, fun _ => rfl⟩
  have hp0 : HasFPowerSeriesAt Q p (u 0) := by
    rw [huapp, zero_smul]; exact hp
  have h1 : HasFPowerSeriesAt (Q ∘ u) (p.compContinuousLinearMap u) 0 :=
    hp0.compContinuousLinearMap
  have h2 : (Q ∘ u) = fun t : 𝕜 => t ^ 2 • Q y := by
    funext t
    simp only [Function.comp_apply, huapp, hQ]
  rw [h2] at h1
  have heq := h1.eq_formalMultilinearSeries (hasFPowerSeriesAt_sqSeries (Q y))
  have key : (p.compContinuousLinearMap u) 2 (fun _ => (1 : 𝕜))
      = sqSeries 𝕜 (Q y) 2 (fun _ => (1 : 𝕜)) := by rw [heq]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply, sqSeries_apply] at key
  simp only [Function.comp_def, huapp, one_smul, Finset.prod_const_one] at key
  simpa using key

end AltCounter
