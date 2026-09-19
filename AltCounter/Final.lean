/-
The general analytic statement is inconsistent: assuming that precomposition on continuous alternating maps is `C^ω`
for all normed spaces over all nontrivially normed fields, we derive `False`.
-/
import AltCounter.Puiseux
import AltCounter.MainNSC

namespace AltCounter

open BoundedContinuousFunction

/-- There is a complete ultrametric nontrivially normed field of characteristic 2, with infinite residue field, which
is not spherically complete. -/
theorem exists_field :
    ∃ (K : Type) (_ : NontriviallyNormedField K), IsUltrametricDist K ∧ CompleteSpace K ∧ CharP K 2 ∧
      InfiniteResidue K ∧ HasEmptyNestedBalls K := by
  obtain ⟨L, _, v, hv⟩ := exists_goodModel
  exact exists_field_of_goodModel v hv

instance instCompleteSpaceF (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] :
    CompleteSpace (F 𝕜) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- **The general `C^ω` statement is false.** -/
theorem false_of_general_contDiff_omega
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E E' F : Type)
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : Type) [Fintype ι],
      ContDiff 𝕜 (⊤ : WithTop ℕ∞)
        (fun f : E →L[𝕜] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False := by
  obtain ⟨K, instK, hult, hcomp, hchar, hres, hballs⟩ := exists_field
  have := hult; have := hcomp; have := hchar
  exact not_contDiff_omega_Q_of_NSC hres (nsc_of_hasEmptyNestedBalls hballs)
    (h K (Linf K) (Linf K) (F K) (Fin 2))

/-- Sharper form: it is already false for Banach spaces over complete ultrametric fields of characteristic 2 and
alternating maps in two variables. -/
theorem false_of_charTwo_banach_contDiff_omega
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]
      (E F : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F],
      ContDiff 𝕜 (⊤ : WithTop ℕ∞)
        (fun f : E →L[𝕜] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin 2]→L[𝕜] F) →L[𝕜] (E [⋀^Fin 2]→L[𝕜] F)))) : False := by
  obtain ⟨K, instK, hult, hcomp, hchar, hres, hballs⟩ := exists_field
  have := hult; have := hcomp; have := hchar
  exact not_contDiff_omega_Q_of_NSC hres (nsc_of_hasEmptyNestedBalls hballs)
    (h K (Linf K) (F K))

end AltCounter
