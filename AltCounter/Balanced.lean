/-
Multivariate-polynomial lemmas in characteristic 2: coefficients at "balanced" squarefree monomials.
Variables are indexed by `ι ⊕ ι` (`inl i` = `X i`, `inr i` = `Y i`).
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.Ideal.Quotient.Basic
import AltCounter.Pfaffian

namespace AltCounter

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The balanced squarefree monomial `∏_{i ∈ S} X_i Y_i`. -/
noncomputable def bal (S : Finset ι) : (ι ⊕ ι) →₀ ℕ :=
  ∑ i ∈ S, (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1)

/-- The monomial `∏_{i ∈ S} x_i ^ 2` in the diagonal variables. -/
noncomputable def dbl (S : Finset ι) : ι →₀ ℕ := ∑ i ∈ S, Finsupp.single i 2

/-- Swap `X ↔ Y`. -/
noncomputable def swapXY : MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial (ι ⊕ ι) R := rename Sum.swap

/-- Substitute `Y_i := X_i`. -/
noncomputable def diagXY : MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial ι R := rename (Sum.elim id id)

/-- For a swap-invariant polynomial in characteristic 2, the coefficient of a balanced monomial can be read
off after the diagonal substitution. -/
theorem coeff_bal_of_swap_invariant [CharP R 2] (f : MvPolynomial (ι ⊕ ι) R) (hf : swapXY f = f)
    (S : Finset ι) : f.coeff (bal S) = (diagXY f).coeff (dbl S) := by
  sorry

/-- A multiple of the square of a variable has zero coefficient at a balanced (squarefree) monomial. -/
theorem coeff_bal_sq_mul (S : Finset ι) (v : ι ⊕ ι) (h : MvPolynomial (ι ⊕ ι) R) :
    (X v ^ 2 * h).coeff (bal S) = 0 := by
  sorry

/-- Frobenius on coefficients in characteristic 2. -/
theorem coeff_two_nsmul_sq [CharP R 2] {σ : Type*} (m : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (f ^ 2).coeff (2 • m) = (f.coeff m) ^ 2 := by
  sorry

/-- **Key identity.** Let `g p q` be polynomials with `g p q (Y, X) = g p q (X, Y) + X_p²Y_q² + X_q²Y_p²`
and `g p q (X, X) = 0`. Then for every perfect matching `σ` of `ι`, the product of the `g` over the edges
of `σ` has coefficient `1` at the balanced monomial `∏_i X_i Y_i`. -/
theorem coeff_bal_prod_matching [CharP R 2] [LinearOrder ι]
    (g : ι → ι → MvPolynomial (ι ⊕ ι) R)
    (hswap : ∀ p q, p ≠ q → swapXY (g p q) = g p q + (X (Sum.inl p) * X (Sum.inr q)) ^ 2
      + (X (Sum.inl q) * X (Sum.inr p)) ^ 2)
    (hdiag : ∀ p q, p ≠ q → diagXY (g p q) = 0)
    (σ : Equiv.Perm ι) (hσ : σ ∈ PM ι) :
    (pfTerm (Matrix.of g) σ).coeff (bal (Finset.univ : Finset ι)) = 1 := by
  sorry

/-- Lower-order perturbations do not change the top coefficient: if `G p q = g p q + c p q` with `g p q`
homogeneous of degree `4` and `c p q` of total degree `≤ 3`, the coefficient at the balanced monomial of
the matching product is unchanged. -/
theorem coeff_bal_pfTerm_perturb [LinearOrder ι]
    (g c : ι → ι → MvPolynomial (ι ⊕ ι) R)
    (hg : ∀ p q, (g p q).IsHomogeneous 4) (hc : ∀ p q, (c p q).totalDegree ≤ 3)
    (σ : Equiv.Perm ι) (hσ : σ ∈ PM ι) :
    (pfTerm (Matrix.of fun p q => g p q + c p q) σ).coeff (bal (Finset.univ : Finset ι))
      = (pfTerm (Matrix.of g) σ).coeff (bal (Finset.univ : Finset ι)) := by
  sorry

end AltCounter
