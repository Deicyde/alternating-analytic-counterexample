/-
Counterexample to analyticity of precomposition on continuous alternating maps in characteristic 2.
Shared definitions.
-/
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Basic

namespace AltCounter

open BoundedContinuousFunction

/-- `ℓ^∞(ℕ, 𝕜)`: bounded sequences with the sup norm (bounded continuous functions on discrete `ℕ`). -/
abbrev Linf (𝕜 : Type*) [NontriviallyNormedField 𝕜] := ℕ →ᵇ 𝕜

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- A function of four `ℓ^∞` arguments that is additive and homogeneous in each slot and bounded by
`C * ‖a‖ * ‖b‖ * ‖x‖ * ‖y‖`. -/
structure IsBdd4 (Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (C : ℝ) : Prop where
  add₁ : ∀ a a' b x y, Λ (a + a') b x y = Λ a b x y + Λ a' b x y
  add₂ : ∀ a b b' x y, Λ a (b + b') x y = Λ a b x y + Λ a b' x y
  add₃ : ∀ a b x x' y, Λ a b (x + x') y = Λ a b x y + Λ a b x' y
  add₄ : ∀ a b x y y', Λ a b x (y + y') = Λ a b x y + Λ a b x y'
  smul₁ : ∀ (c : 𝕜) a b x y, Λ (c • a) b x y = c * Λ a b x y
  smul₂ : ∀ (c : 𝕜) a b x y, Λ a (c • b) x y = c * Λ a b x y
  smul₃ : ∀ (c : 𝕜) a b x y, Λ a b (c • x) y = c * Λ a b x y
  smul₄ : ∀ (c : 𝕜) a b x y, Λ a b x (c • y) = c * Λ a b x y
  bound : ∀ a b x y, ‖Λ a b x y‖ ≤ C * ‖a‖ * ‖b‖ * ‖x‖ * ‖y‖

/-- The multilinear Phillips property: bounded 4-linear forms on `ℓ^∞` are uniformly small as soon as one
argument is supported far out. It holds for every complete non-archimedean field that is not
spherically complete (there `(ℓ^∞)' = c₀`), and fails for spherically complete fields. -/
def TailProperty : Prop :=
  ∀ (Λ : Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → Linf 𝕜 → 𝕜) (C : ℝ), IsBdd4 𝕜 Λ C → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ a b x y : Linf 𝕜, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ((∀ i < N, a i = 0) ∨ (∀ i < N, b i = 0) ∨ (∀ i < N, x i = 0) ∨ (∀ i < N, y i = 0)) →
      ‖Λ a b x y‖ ≤ ε

end AltCounter
