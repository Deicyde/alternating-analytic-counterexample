/-
Determinants of symmetric zero-diagonal matrices in characteristic 2 as sums of squares over perfect matchings.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

namespace AltCounter

open Finset

variable {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Perfect matchings of `α`, encoded as fixed-point-free involutions. -/
def PM (α : Type*) [Fintype α] [DecidableEq α] : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

/-- The product of the entries of `B` over the edges `{i, σ i}`, `i < σ i`, of a matching. -/
def pfTerm (B : Matrix α α R) (σ : Equiv.Perm α) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), B i (σ i)

/-- In characteristic 2 the determinant of a symmetric matrix with zero diagonal is the sum over perfect
matchings of the squares of the matching products (so it is the square of the "Pfaffian"). -/
theorem det_eq_sum_PM_sq [CharP R 2] (B : Matrix α α R) (hsymm : ∀ i j, B i j = B j i)
    (hdiag : ∀ i, B i i = 0) : B.det = ∑ σ ∈ PM α, (pfTerm B σ) ^ 2 := by
  sorry

/-- The number of perfect matchings of a set of even cardinality is odd. -/
theorem card_PM_odd (h : Even (Fintype.card α)) : Odd (PM α).card := by
  sorry

end AltCounter
