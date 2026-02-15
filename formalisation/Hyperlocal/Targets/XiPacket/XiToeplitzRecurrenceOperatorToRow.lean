/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceOperatorToRow.lean

  Patch: remove the last `sorry` in `toeplitzRow3_of_jetQuotOp_eq_zero`.

  Key point:
  * use the existing coordinate-expansion lemma `toeplitzL_two_apply_fin0`
    (from `...ToeplitzLToRow3`) instead of expanding `toeplitzL` via shifts here.
  * when taking real parts, kill the `im`-terms using *all three* facts:
      `JetQuotOp.aRk1_im0`, `JetQuotOp.aRk1_im1`, `JetQuotOp.aRk1_im2`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperator
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3

/-- The real row-vector extracted from the `toeplitzL 2` coefficients (the row giving the dot product). -/
def jetQuotRow3 (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  fun i => Complex.re (JetQuotOp.aRk1 s i)

/-!
### From row-0 operator output to a real `toeplitzRow3` constraint

Route B only consumes the row-0 scalar output
`(JetQuotOp.jetQuotToeplitzOp3 s w) 0 = 0`.

The stronger hypothesis `JetQuotOp.jetQuotToeplitzOp3 s w = 0` is not expected to hold
for canonical windows (see `...XiToeplitzRecurrenceToeplitzLImpossibility`).
-/

/--
If the jet-quotient Toeplitz operator vanishes at coordinate `0`, then the extracted real
row gives a `toeplitzRow3` constraint on `reVec3 w`.

We take coordinate `0` (matching the `toeplitzL_two_apply_fin0` convention).
-/
lemma toeplitzRow3_of_jetQuotOp_fin0_eq_zero
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h0 : (JetQuotOp.jetQuotToeplitzOp3 s w) (0 : Fin 3) = 0) :
    toeplitzRow3 (jetQuotRow3 s) (reVec3 w) := by
  classical

  -- Rewrite `jetQuotToeplitzOp3` as `toeplitzL 2 ...` and expand row-0.
  have hsum :
      ((JetQuotOp.aRk1 s 0) * w 0 + (JetQuotOp.aRk1 s 1) * w 1) + (JetQuotOp.aRk1 s 2) * w 2 = 0 := by
    simpa [JetQuotOp.jetQuotToeplitzOp3, toeplitzL_two_apply_fin0] using h0

  -- Take real parts; kill the `im`-terms using `aRk1_im0/im1/im2`.
  have hre :
      (JetQuotOp.aRk1 s 0).re * (w 0).re
    + (JetQuotOp.aRk1 s 1).re * (w 1).re
    + (JetQuotOp.aRk1 s 2).re * (w 2).re = 0 := by
    have hre0 := congrArg Complex.re hsum
    simpa [Complex.add_re, Complex.mul_re,
      JetQuotOp.aRk1_im0, JetQuotOp.aRk1_im1, JetQuotOp.aRk1_im2,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hre0

  -- Rewrite as a `Fin 3` sum and finish.
  have hfin :
      (∑ i : Fin 3, jetQuotRow3 s i * (reVec3 w) i) = 0 := by
    simpa [jetQuotRow3, reVec3, Fin.sum_univ_three,
      add_assoc, add_left_comm, add_comm] using hre

  simpa [toeplitzRow3] using hfin

/-- Backwards-compatible wrapper: full-window annihilation implies the row-0 hypothesis. -/
lemma toeplitzRow3_of_jetQuotOp_eq_zero
    (s : Hyperlocal.OffSeed Xi) (w : Window 3)
    (h : JetQuotOp.jetQuotToeplitzOp3 s w = 0) :
    toeplitzRow3 (jetQuotRow3 s) (reVec3 w) := by
  classical
  have h0 : (JetQuotOp.jetQuotToeplitzOp3 s w) (0 : Fin 3) = 0 := by
    simpa using congrArg (fun f : Window 3 => f (0 : Fin 3)) h
  exact toeplitzRow3_of_jetQuotOp_fin0_eq_zero (s := s) (w := w) h0

end Hyperlocal.Targets.XiPacket
