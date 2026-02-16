/-
File: formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

Delete the old axiom gate here and import the analytic boundary instead.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Analytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-!
## Reduced semantic gate: scalar goals (explicit ℂ-identities)

`xiJetQuot_row0_scalarGoals` is now provided by the analytic boundary module
`...Row0Analytic.lean` as a `def` (with 4 proof obligations).
-/

/--
Backwards-compatibility: recover the original witness bundle required by
`XiToeplitzRecurrenceJetQuotientRow0Correctness.lean` and downstream.
-/
def xiJetQuot_row0_witnessC (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0WitnessC s :=
  witnessC_of_scalarGoals (s := s) (xiJetQuot_row0_scalarGoals (s := s))

open Hyperlocal.Transport

/-- Canonical row-0 identity for `w0`. -/
theorem xiJetQuot_row0_w0 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_witnessC (s := s)).hop_w0

/-- Canonical row-0 identity for `wc`. -/
theorem xiJetQuot_row0_wc (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_witnessC (s := s)).hop_wc

/-- Canonical row-0 identity for `wp2`. -/
theorem xiJetQuot_row0_wp2 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_witnessC (s := s)).hop_wp2

/-- Canonical row-0 identity for `wp3`. -/
theorem xiJetQuot_row0_wp3 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_witnessC (s := s)).hop_wp3

end XiPacket
end Targets
end Hyperlocal
