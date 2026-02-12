/-
  formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientEllFromOperator.lean

  FIX: your environment is not seeing `ell_eq_zero_of_toeplitzRow3` (even when imported),
  so make this file self-contained by using a *private local* lemma with a different name.

  This unblocks commits while keeping `XiToeplitzRecurrenceStencilToEll.lean` intact.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperator
import Hyperlocal.MinimalModelNonvanishing
import Hyperlocal.Cancellation.Recurrence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Local fallback: stencil (left-kernel) ⇒ `ell = 0`. -/
private theorem ell_eq_zero_of_toeplitzRow3_local
    (u0 uc v : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    (hc0 : c ≠ 0)
    (h0 : toeplitzRow3 c u0)
    (hc : toeplitzRow3 c uc)
    (hv : toeplitzRow3 c v) :
    Transport.ell u0 uc v = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) ℝ := Transport.colsMat u0 uc v

  have hmul : M.transpose.mulVec c = 0 := by
    ext j
    fin_cases j
    ·
      have : (∑ i : Fin 3, u0 i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using h0
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this
    ·
      have : (∑ i : Fin 3, uc i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using hc
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this
    ·
      have : (∑ i : Fin 3, v i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using hv
      simpa [Matrix.mulVec, Matrix.transpose_apply, M, Transport.colsMat, Transport.baseMat] using this

  have hdetT : (M.transpose).det = 0 := by
    by_contra hne
    have hUnitDet : IsUnit (M.transpose).det := (isUnit_iff_ne_zero).2 hne
    have hUnitM : IsUnit (M.transpose) :=
      (Matrix.isUnit_iff_isUnit_det (A := M.transpose)).2 hUnitDet
    have hinj : Function.Injective (M.transpose.mulVec) :=
      (Matrix.mulVec_injective_iff_isUnit (A := M.transpose)).2 hUnitM
    have : c = 0 := by
      apply hinj
      simpa [hmul]
    exact hc0 (by simpa [this])

  have hdet : M.det = 0 := by
    simpa [Matrix.det_transpose] using hdetT
  simpa [Transport.ell, M] using hdet

/-- (B1 semantic subgoal) operator/recurrence extraction yields a stencil for p=2. -/
axiom xiJetQuotStencil_fromOperator2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    toeplitzRow3 c2 (reVec3 (w0 s)) ∧
    toeplitzRow3 c2 (reVec3 (wc s)) ∧
    toeplitzRow3 c2 (reVec3 (wp2 s))

/-- (B1 semantic subgoal) operator/recurrence extraction yields a stencil for p=3. -/
axiom xiJetQuotStencil_fromOperator3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    toeplitzRow3 c3 (reVec3 (w0 s)) ∧
    toeplitzRow3 c3 (reVec3 (wc s)) ∧
    toeplitzRow3 c3 (reVec3 (wp3 s))

theorem xiJetQuotEll_spec2_theorem (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 := by
  rcases xiJetQuotStencil_fromOperator2 s with ⟨c2, hc2, h0, hc, hp⟩
  exact ell_eq_zero_of_toeplitzRow3_local
    (u0 := reVec3 (w0 s)) (uc := reVec3 (wc s)) (v := reVec3 (wp2 s))
    (c := c2) hc2 h0 hc hp

theorem xiJetQuotEll_spec3_theorem (s : Hyperlocal.OffSeed Xi) :
  Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 := by
  rcases xiJetQuotStencil_fromOperator3 s with ⟨c3, hc3, h0, hc, hp⟩
  exact ell_eq_zero_of_toeplitzRow3_local
    (u0 := reVec3 (w0 s)) (uc := reVec3 (wc s)) (v := reVec3 (wp3 s))
    (c := c3) hc3 h0 hc hp

end Hyperlocal.Targets.XiPacket
