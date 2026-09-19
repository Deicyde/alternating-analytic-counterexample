/-
Ultrametric bounds for determinants: stability under small perturbations, and smallness of the determinant
of a matrix that is close to a matrix of small rank.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Basic
import AltCounter.Defs

namespace AltCounter

open Finset Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] {N : ℕ}

/-- Ultrametric Hadamard-type bound. -/
theorem norm_det_le_prod (A : Matrix (Fin N) (Fin N) 𝕜) (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hA : ∀ i j, ‖A i j‖ ≤ c i) : ‖A.det‖ ≤ ∏ i, c i := by
  sorry

/-- Stability: if `‖G.det‖ ≥ 1`, the entries of `G` are bounded by `C ≥ 1`, and the entries of `E` by `ε` with
`ε * C ^ (N - 1) < 1`, then `‖(G + E).det‖ ≥ 1`. -/
theorem one_le_norm_det_add (G E : Matrix (Fin N) (Fin N) 𝕜) (C ε : ℝ) (hC : 1 ≤ C) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1)
    (hG : ∀ i j, ‖G i j‖ ≤ C) (hE : ∀ i j, ‖E i j‖ ≤ ε) (hsmall : ε * C ^ (N - 1) < 1)
    (hdet : 1 ≤ ‖G.det‖) : 1 ≤ ‖(G + E).det‖ := by
  sorry

/-- If `A` (entries bounded by `C ≥ 1`) is within `η ≤ 1` of a matrix of the form `∑_{k < r} u_k ⊗ v_k`
and `r ≤ N`, then `‖A.det‖ ≤ C ^ r * η ^ (N - r)`. -/
theorem norm_det_le_of_close_to_lowrank (A : Matrix (Fin N) (Fin N) 𝕜) (C η : ℝ) (hC : 1 ≤ C)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ C) (r : ℕ) (hr : r ≤ N)
    (u v : Fin r → Fin N → 𝕜) (hclose : ∀ i j, ‖A i j - ∑ k, u k i * v k j‖ ≤ η) :
    ‖A.det‖ ≤ C ^ r * η ^ (N - r) := by
  sorry

end AltCounter
