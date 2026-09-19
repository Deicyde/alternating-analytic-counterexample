/-
The finite identity: for every "lift" on a block of even size there is a point of the unit polydisc at which
the block matrix has determinant of norm `≥ 1`.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import AltCounter.Balanced
import AltCounter.GaussPoint

namespace AltCounter

open BoundedContinuousFunction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The sequence supported on the block `[s, s + n)` with entries `x`. -/
noncomputable def blockVec {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) : Linf 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => if h : s ≤ k ∧ k < s + n then x ⟨k - s, by omega⟩ else 0) (∑ i, ‖x i‖) (by
      intro k
      split_ifs with h
      · exact Finset.single_le_sum (f := fun i => ‖x i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ _)
      · simpa using Finset.sum_nonneg (fun i _ => norm_nonneg (x i)))

theorem blockVec_apply_block {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (i : Fin n) :
    blockVec s x (s + i) = x i := by
  sorry

theorem blockVec_apply_of_lt {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (k : ℕ) (hk : k < s) :
    blockVec s x k = 0 := by
  sorry

theorem blockVec_apply_of_ge {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (k : ℕ) (hk : s + n ≤ k) :
    blockVec s x k = 0 := by
  sorry

theorem norm_blockVec_le {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖blockVec s x‖ ≤ 1 := by
  sorry

/-- If `a'` vanishes from `s` on and `‖a'‖ ≤ 1`, `‖x i‖ ≤ 1`, then `‖a' + blockVec s x‖ ≤ 1`. -/
theorem norm_add_blockVec_le {n : ℕ} (s : ℕ) (x : Fin n → 𝕜) (hx : ∀ i, ‖x i‖ ≤ 1) (a' : Linf 𝕜)
    (ha' : ∀ k, s ≤ k → a' k = 0) (hn : ‖a'‖ ≤ 1) : ‖a' + blockVec s x‖ ≤ 1 := by
  sorry

variable [IsUltrametricDist 𝕜]

/-- **Finite lemma.** For a family `Λ p q` of bounded 4-linear forms on `ℓ^∞` which is alternating in the last
two slots, symmetric with zero diagonal in `(p, q)`, and restricts on the diagonal `a = b` to
`W(a x, a y)_{pq}`, every block of even size `n` admits unit vectors `x, y` for which the `n × n` block of
`Λ (a' + x) (b' + y) (a' + x) (b' + y)` has determinant of norm at least `1`. -/
theorem exists_block_point [CharP 𝕜 2] (hres : InfiniteResidue 𝕜)
    (Λ : ℕ → ℕ → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (C : ℝ)
    (hlin : ∀ p q, IsBdd4 𝕜 (Λ p q) C)
    (halt : ∀ p q a b x, Λ p q a b x x = 0)
    (hdiag : ∀ p q a x y, Λ p q a a x y = a p * x p * (a q * y q) + a p * y p * (a q * x q))
    (hsymm : ∀ p q a b x y, Λ p q a b x y = Λ q p a b x y)
    (hzero : ∀ p a b x y, Λ p p a b x y = 0)
    (n : ℕ) (hn : Even n) (s : ℕ) (a' b' : Linf 𝕜)
    (ha' : ∀ k, s ≤ k → a' k = 0) (hb' : ∀ k, s ≤ k → b' k = 0) :
    ∃ x y : Fin n → 𝕜, (∀ i, ‖x i‖ ≤ 1) ∧ (∀ i, ‖y i‖ ≤ 1) ∧
      1 ≤ ‖(Matrix.of fun p q : Fin n =>
        Λ (s + p) (s + q) (a' + blockVec s x) (b' + blockVec s y)
          (a' + blockVec s x) (b' + blockVec s y)).det‖ := by
  sorry

end AltCounter
