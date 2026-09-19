/-
Comparator solution: proves the two theorems of `Challenge.lean` verbatim, from the project's formalization.
-/
import AltCounter.Final

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
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False :=
  AltCounter.false_of_general_contDiff_omega h

/-- Sharper form: the analytic statement is already inconsistent when restricted to complete ultrametric fields of
characteristic 2, Banach spaces, `E' = E`, and alternating maps in two variables. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM_charTwo_banach
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
      (E F : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin 2]→L[𝕜] F) →L[𝕜] (E [⋀^Fin 2]→L[𝕜] F)))) : False :=
  AltCounter.false_of_charTwo_banach_contDiff_omega h

end AlternatingAnalyticChallenge
