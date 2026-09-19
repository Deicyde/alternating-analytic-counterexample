/-
The counterexample with the field hypothesis in its classical form: `(ℓ^∞ / c₀)' = 0`
(van der Put 1969, Thm 3.2: a complete non-archimedean field that is not spherically complete satisfies it;
only this implication is needed to exhibit a field to which the theorem applies).
-/
import AltCounter.Main
import AltCounter.Phillips

namespace AltCounter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [CompleteSpace 𝕜] [CharP 𝕜 2]

/-- Over a complete ultrametric field of characteristic 2 with infinite residue field and with
`(ℓ^∞ / c₀)' = 0`, precomposition on continuous alternating 2-forms `ℓ^∞ × ℓ^∞ → F` is not analytic at `0`. -/
theorem not_analyticAt_Q_of_NSC (hres : InfiniteResidue 𝕜) (hnsc : NSC 𝕜) :
    ¬ AnalyticAt 𝕜 (Q 𝕜) 0 :=
  not_analyticAt_Q hres (tailProperty_of_NSC hnsc)

/-- In particular it is not `C^ω` (`(⊤ : WithTop ℕ∞)` is the analytic exponent `ω`). -/
theorem not_contDiff_omega_Q_of_NSC (hres : InfiniteResidue 𝕜) (hnsc : NSC 𝕜) :
    ¬ ContDiff 𝕜 (⊤ : WithTop ℕ∞) (Q 𝕜) :=
  not_contDiff_omega_Q hres (tailProperty_of_NSC hnsc)

end AltCounter
