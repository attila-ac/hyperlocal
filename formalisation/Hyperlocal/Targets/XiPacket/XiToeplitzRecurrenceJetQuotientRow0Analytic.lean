/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Analytic.lean

  Row-0 analytic bridge (stabilised): consume only row0Sigma = 0 facts.

  FIX (robust):
  Do NOT reference Route–C frontier axiom names (`JetQuotOp.*`) from here.
  Instead consume only the root-level stable theorems exported by
  `XiRow0Bridge_CauchyConvolutionDischarge.lean`:

    row0Sigma_w0_eq_zero, row0Sigma_wc_eq_zero, row0Sigma_wp2_eq_zero, row0Sigma_wp3_eq_zero.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open Complex
open scoped BigOperators

/--
Route-C/Route-A: analytic discharge of the row-0 scalar goals.

This file is intentionally immune to any naming refactors inside `JetQuotOp`.
It depends only on the four exported root-level row0Sigma=0 theorems.
-/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    simpa using (_root_.Hyperlocal.Targets.XiPacket.row0Sigma_w0_eq_zero s)
  hwc := by
    simpa using (_root_.Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero s)
  hwp2 := by
    simpa using (_root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp2_eq_zero s)
  hwp3 := by
    simpa using (_root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp3_eq_zero s)

/-- Public stable name (consumed downstream). -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end Hyperlocal.Targets.XiPacket
