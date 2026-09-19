/-
Comparator challenge (Mathlib only; every constant in the statements is a Mathlib constant).

**The analytic version of "precomposition on continuous alternating maps is smooth" is false.**

For normed spaces `E, E', F` over a nontrivially normed field `𝕜` and a finite index type `ι`, the map
`f ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM f` (`m ↦ m ∘ (f, …, f)`) from `E →L[𝕜] E'` to
`(E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)` is `C^n` for every `n : ℕ∞` in every characteristic, and `C^ω` when
`(card ι)!` is invertible in `𝕜`. One would like to have the `C^ω` statement in full generality (it is what an analytic
vector-bundle structure on bundles of continuous alternating maps needs). The challenge is to show that this general
statement is inconsistent: assume it, and derive `False`.

(The obstruction lives in characteristic 2, over a complete non-archimedean field which is not spherically complete,
with `E = E' = ℓ^∞` and `ι = Fin 2`; the second theorem records that the statement already fails in that restricted
setting.)
-/
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Defs

open scoped ContDiff

namespace AlternatingAnalyticChallenge

/-- Assume the general analytic statement: for all nontrivially normed fields `𝕜`, all normed spaces `E, E', F` over
`𝕜` and all finite index types `ι`, precomposition `f ↦ (m ↦ m ∘ (f, …, f))` on continuous alternating maps is `C^ω`.
Then `False`. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E E' F : Type)
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : Type) [Fintype ι],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False := by
  sorry

/-- Sharper form: the analytic statement is already inconsistent when restricted to complete ultrametric fields of
characteristic 2, Banach spaces, `E' = E`, and alternating maps in two variables. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM_charTwo_banach
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
      (E F : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin 2]→L[𝕜] F) →L[𝕜] (E [⋀^Fin 2]→L[𝕜] F)))) : False := by
  sorry

end AlternatingAnalyticChallenge
