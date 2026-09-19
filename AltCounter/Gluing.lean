/-
Gluing: the core contradiction.
-/
import AltCounter.FiniteLemma
import AltCounter.DetBounds

namespace AltCounter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜]

/-- **Core theorem.** Over an ultrametric field of characteristic 2 with infinite residue field and the
multilinear Phillips (tail) property, there is no family `Λ p q` of uniformly bounded 4-linear forms on `ℓ^∞`
which (i) is alternating in the last two slots, (ii) equals `W(a x, a y)_{pq}` on the diagonal `a = b`,
(iii) is symmetric with zero diagonal in `(p, q)`, and (iv) has all its value matrices `(Λ p q a b x y)_{p q}`
uniformly approximable by matrices of finite rank. -/
theorem core_false [CharP 𝕜 2] (hres : InfiniteResidue 𝕜) (htail : TailProperty 𝕜)
    (Λ : ℕ → ℕ → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (C : ℝ) (hC : 1 ≤ C)
    (hlin : ∀ p q, IsBdd4 𝕜 (Λ p q) C)
    (halt : ∀ p q a b x, Λ p q a b x x = 0)
    (hdiag : ∀ p q a x y, Λ p q a a x y = a p * x p * (a q * y q) + a p * y p * (a q * x q))
    (hsymm : ∀ p q a b x y, Λ p q a b x y = Λ q p a b x y)
    (hzero : ∀ p a b x y, Λ p p a b x y = 0)
    (happrox : ∀ a b x y : Linf 𝕜, ∀ η : ℝ, 0 < η → ∃ (r : ℕ) (u v : Fin r → ℕ → 𝕜),
      ∀ p q, ‖Λ p q a b x y - ∑ k, u k p * v k q‖ ≤ η) : False := by
  sorry

end AltCounter
