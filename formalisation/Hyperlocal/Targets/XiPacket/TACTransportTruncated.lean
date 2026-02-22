/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated.lean

  Manuscript v4.1 “TAC Transport” algebra, formalised *purely finitely*.

  Finite Toeplitz jet-transport matrix T(δ) on `Fin N` jets, and invertibility
  via “upper-triangular with diagonal 1”.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC

/-- The finite Toeplitz transport matrix `T(δ)` on `Fin N` jets.

`Tδ j m = δ^(m-j)/(m-j)!` for `m≥j`, else `0`.
-/
def transportMat (N : ℕ) (δ : ℂ) : Matrix (Fin N) (Fin N) ℂ := fun j m =>
  if h : (j : ℕ) ≤ (m : ℕ) then
    δ ^ ((m : ℕ) - (j : ℕ)) / (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
  else
    0

/-- The transported jet vector `Γ ↦ T(δ) Γ` in matrix form. -/
def transport (N : ℕ) (δ : ℂ) (Γ : Fin N → ℂ) : Fin N → ℂ :=
  (transportMat N δ).mulVec Γ

@[simp] lemma transportMat_diag (N : ℕ) (δ : ℂ) (j : Fin N) :
    transportMat N δ j j = 1 := by
  classical
  simp [transportMat]

/-- Determinant of the transport matrix is `1` (upper triangular with ones on the diagonal). -/
theorem det_transportMat (N : ℕ) (δ : ℂ) :
    Matrix.det (transportMat N δ) = 1 := by
  classical
  -- below-diagonal entries are 0
  have hbelow : ∀ i j : Fin N, j < i → transportMat N δ i j = 0 := by
    intro i j hij
    have hnot : ¬ ((i : ℕ) ≤ (j : ℕ)) := by
      exact not_le_of_gt (Fin.lt_iff_val_lt_val.mp hij)
    simp [transportMat, hnot]

  -- Package as BlockTriangular w.r.t. `id` (this is what `det_of_upperTriangular` wants here).
  have hblock : Matrix.BlockTriangular (transportMat N δ) id := by
    intro i j hij
    -- `hij : id j < id i` is definitional `j < i`
    exact hbelow i j hij

  -- In this Mathlib snapshot, `det_of_upperTriangular` takes `h : BlockTriangular M id`
  -- as an explicit argument, with `M` implicit.
  -- It returns: det M = ∏ i, M i i.
  simpa [transportMat_diag] using (Matrix.det_of_upperTriangular (h := hblock))

/-- The transport matrix is invertible over `ℂ` (as a unit in the matrix ring). -/
theorem transportMat_isUnit (N : ℕ) (δ : ℂ) :
    IsUnit (transportMat N δ) := by
  classical
  -- In a commutative ring, matrix is a unit iff det is a unit.
  refine (Matrix.isUnit_iff_isUnit_det (A := transportMat N δ)).2 ?_
  have hdet : Matrix.det (transportMat N δ) = 1 := det_transportMat (N := N) (δ := δ)
  -- det = 1 is a unit
  simpa [hdet] using (show IsUnit (1 : ℂ) from isUnit_one)

/-- The transport map `Γ ↦ T(δ) Γ` is injective. -/
theorem transport_injective (N : ℕ) (δ : ℂ) :
    Function.Injective (transport N δ) := by
  classical
  have hU : IsUnit (transportMat N δ) := transportMat_isUnit (N := N) (δ := δ)
  -- lemma you grepped in `Matrix/NonsingularInverse.lean`
  simpa [transport] using
    (Matrix.mulVec_injective_iff_isUnit (A := transportMat N δ)).2 hU

end TAC

end XiPacket
end Targets
end Hyperlocal
