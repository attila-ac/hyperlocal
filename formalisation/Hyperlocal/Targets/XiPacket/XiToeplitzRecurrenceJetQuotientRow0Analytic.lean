/-
File: formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Analytic.lean

Change the analytic boundary from an axiom to a constructor (with 4 proof holes).
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Scalarize
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Route-B analytic output (row-0):
σ-sum kills the four canonical ξ-windows (w0, wc, wp2, wp3).

This is now a *constructor* (Type-valued), with exactly four remaining proof obligations.
-/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
  XiJetQuotRow0ScalarGoals s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (A) row0Sigma kills w0
    -- goal: row0Sigma s (w0 s) = 0
    sorry
  · -- (B) row0Sigma kills wc
    -- goal: row0Sigma s (wc s) = 0
    sorry
  · -- (C) row0Sigma kills wp2
    -- goal: row0Sigma s (wp2 s) = 0
    sorry
  · -- (D) row0Sigma kills wp3
    -- goal: row0Sigma s (wp3 s) = 0
    sorry

/-- Stable downstream name (must be a `def` since the codomain is a `Type`). -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
  XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end XiPacket
end Targets
end Hyperlocal
