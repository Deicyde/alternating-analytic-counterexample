/-
An analytic map which is homogeneous of degree 2 is the diagonal of a continuous bilinear map
(in every characteristic: uniqueness of one-variable power series coefficients).
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions

namespace AltCounter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem exists_bilinear_of_analyticAt_of_homogeneous (Q : X → Z)
    (hQ : ∀ (c : 𝕜) (f : X), Q (c • f) = c ^ 2 • Q f) (h : AnalyticAt 𝕜 Q 0) :
    ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => X) Z, ∀ f, P (fun _ => f) = Q f := by
  sorry

end AltCounter
