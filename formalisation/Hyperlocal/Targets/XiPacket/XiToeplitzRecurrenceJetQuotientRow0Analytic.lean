/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Analytic.lean

  Row-0 analytic bridge (stabilised): consume only row0Sigma = 0 facts.

  FIX:
  Do NOT rely on any exported root-level names like `row0Sigma_w0_eq_zero`
  (they are currently not in the environment at the expected name).

  Instead, build the four scalar-goal fields *directly* from:
    • the Route–C semantic gate axioms `JetQuotOp.jetConv_*`
    • the core discharge lemma `row0Sigma_eq_zero_from_JetConvolutionRev`
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

We *inline* the proof of each field from the Route–C semantic gate axioms
(`JetQuotOp.jetConv_*`) to avoid any namespace/name churn on exported theorems.
-/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    -- goal: row0Sigma s (w0 s) = 0
    exact row0Sigma_eq_zero_from_JetConvolutionRev
      (s := s) (z := s.ρ) (w := w0 s) (JetQuotOp.jetConv_w0 s)
  hwc := by
    exact row0Sigma_eq_zero_from_JetConvolutionRev
      (s := s) (z := (1 - s.ρ)) (w := wc s) (JetQuotOp.jetConv_wc s)
  hwp2 := by
    exact row0Sigma_eq_zero_from_JetConvolutionRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2 s) (JetQuotOp.jetConv_wp2 s)
  hwp3 := by
    exact row0Sigma_eq_zero_from_JetConvolutionRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3 s) (JetQuotOp.jetConv_wp3 s)

/-- Public stable name (consumed downstream). -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end Hyperlocal.Targets.XiPacket
