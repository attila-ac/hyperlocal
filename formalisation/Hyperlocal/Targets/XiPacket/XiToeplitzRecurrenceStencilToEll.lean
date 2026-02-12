/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceStencilToEll.lean

  Public “forward bridge” (stencil ⇒ EllOut), matching your existing
  EllOut ⇒ stencil bridge in XiToeplitzRecurrenceEllToStencil.lean.

  This is the missing convenience lemma you’ll want in Step B1 if you end up
  deriving stencils from the jet-quotient recurrence/operator and then
  discharge EllOut.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Stencil (nontrivial left-kernel vector) ⇒ `ell = 0`. -/
theorem ell_eq_zero_of_toeplitzRow3
    (u0 uc v : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    (hc0 : c ≠ 0)
    (h0 : toeplitzRow3 c u0)
    (hc : toeplitzRow3 c uc)
    (hv : toeplitzRow3 c v) :
    Transport.ell u0 uc v = 0 := by
  classical
  -- Let M be the 3×3 column matrix [u0 uc v].
  let M : Matrix (Fin 3) (Fin 3) ℝ := Transport.colsMat u0 uc v

  -- Convert the three dot-product hypotheses into `Mᵀ * c = 0`.
  have hmul : M.transpose.mulVec c = 0 := by
    ext j
    fin_cases j
    · -- column 0
      have : (∑ i : Fin 3, u0 i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using h0
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this
    · -- column 1
      have : (∑ i : Fin 3, uc i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using hc
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this
    · -- column 2
      have : (∑ i : Fin 3, v i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using hv
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this

  -- If det(Mᵀ) ≠ 0 then Mᵀ is a unit, hence mulVec is injective, contradiction.
  have hdetT : (M.transpose).det = 0 := by
    by_contra hne
    have hUnitDet : IsUnit (M.transpose).det := (isUnit_iff_ne_zero).2 hne
    have hUnitM : IsUnit (M.transpose) := (Matrix.isUnit_iff_isUnit_det (A := M.transpose)).2 hUnitDet
    have hinj : Function.Injective (M.transpose.mulVec) :=
      (Matrix.mulVec_injective_iff_isUnit (A := M.transpose)).2 hUnitM
    have : c = 0 := by
      -- compare `mulVec c = 0` with `mulVec 0 = 0`
      apply hinj
      simpa [hmul]
    exact hc0 (by simpa [this])

  -- det(Mᵀ)=0 ⇒ det(M)=0, hence ell=0.
  have hdet : M.det = 0 := by
    simpa [Matrix.det_transpose] using hdetT
  simpa [Transport.ell, M] using hdet

end Hyperlocal.Targets.XiPacket
