/-
A polynomial over an ultrametric field with infinite residue field that has a coefficient of norm `≥ 1`
takes a value of norm `≥ 1` somewhere on the unit polydisc.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange
import AltCounter.Defs

namespace AltCounter

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜]

/-- One-variable case. -/
theorem exists_unit_eval_poly (hres : InfiniteResidue 𝕜) (f : Polynomial 𝕜) (k : ℕ)
    (hk : 1 ≤ ‖f.coeff k‖) : ∃ t : 𝕜, ‖t‖ ≤ 1 ∧ 1 ≤ ‖f.eval t‖ := by
  sorry

/-- Several variables. -/
theorem exists_unit_eval {σ : Type*} [Fintype σ] (hres : InfiniteResidue 𝕜) (f : MvPolynomial σ 𝕜)
    (m : σ →₀ ℕ) (hm : 1 ≤ ‖f.coeff m‖) :
    ∃ z : σ → 𝕜, (∀ i, ‖z i‖ ≤ 1) ∧ 1 ≤ ‖eval z f‖ := by
  sorry

end AltCounter
