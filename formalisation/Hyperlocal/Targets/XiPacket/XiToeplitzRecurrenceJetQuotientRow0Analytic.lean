/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Analytic.lean

  Row-0 analytic bridge.

  UPDATED:
  The four “row0Sigma_* = eval” facts are no longer axioms here.
  They are sourced from the Route–C semantic gate file
    `XiRow0Bridge_CauchyProductAttempt.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

/--
Route-A: analytic discharge of the row-0 scalar goals.

This now consumes the *theorem-level* bridge lemmas exported by
`XiRow0Bridge_CauchyProductAttempt` (currently they depend on the four
`jetConv_*` axioms there, but the semantic boundary is single-sourced).
-/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    rw [row0Sigma_w0_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).1
  hwc := by
    rw [row0Sigma_wc_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.2.1
  hwp2 := by
    rw [row0Sigma_wp2_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.1
  hwp3 := by
    rw [row0Sigma_wp3_eq_eval (s := s)]
    simpa using (R_quartet_zeros s).2.2.2

/-- Public stable name (consumed downstream). -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end XiPacket
end Targets
end Hyperlocal
