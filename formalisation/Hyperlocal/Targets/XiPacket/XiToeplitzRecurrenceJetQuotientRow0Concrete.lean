/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

  NEXT STEP (no refactor, pure semantic burden reduction):

  Replace the old axiom-level semantic gate

    `xiJetQuot_row0_witnessC : XiJetQuotRow0WitnessC s`

  by a strictly smaller axiom stated in the fully scalarised normal form

    `xiJetQuot_row0_scalarGoals : XiJetQuotRow0ScalarGoals s`

  and recover the original witness bundle *definitionally* via
  `witnessC_of_scalarGoals` from the proof/scalarisation file.

  Downstream files should continue to depend on `xiJetQuot_row0_witnessC`
  with no changes.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-!
## Reduced semantic gate: scalar goals (explicit ℂ-identities)

We keep the same downstream-facing name `xiJetQuot_row0_witnessC`,
but the *only* remaining semantic axiom is now the four scalar identities
in the unfolded row-0 form (`row0Sigma`).
-/

/-- NEW smaller semantic gate: the four explicit row-0 scalar identities. -/
axiom xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
  XiJetQuotRow0ScalarGoals s

/--
Backwards-compatibility: recover the original witness bundle required by
`XiToeplitzRecurrenceJetQuotientRow0Correctness.lean` and downstream.

NOTE: `XiJetQuotRow0WitnessC s` is a `Type`, so this must be a `def`, not a `theorem`.
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
