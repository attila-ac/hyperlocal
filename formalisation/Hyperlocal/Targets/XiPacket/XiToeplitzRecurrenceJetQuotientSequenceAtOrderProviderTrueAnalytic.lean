/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean

  TRUE-ANALYTIC landing pad for the Rec2AtOrder provider instance (FULL R0).

  Goal (final):
    instance : XiJetQuotRec2AtOrderProvider

  DAG contract:
  * Only "true analytic" imports (FE/RC/factorisation/jet identities / manuscript).
  * MUST NOT import extractor-facing modules.
  * MUST NOT import Row012 analytic endpoint modules, i.e.
      XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean
    or anything that depends on it.

  Today: staged with three local axioms (one per AtOrder window recurrence).
  Replace them one-by-one by real analytic theorems, then delete the axioms.

  Once this instance is theorem-level, you can switch the public surface import from:
    ...SequenceAtOrderProviderFromAnalyticExtractor
  to:
    ...SequenceAtOrderProviderTrueAnalytic
  with zero downstream changes.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

-- IMPORTANT: do NOT import any "...AnalyticExtractor" / "...AnalyticAxiom" modules here.

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## True analytic surface (3 subgoals)

These are exactly the three recurrence facts to prove from FE/RC/factorisation/manuscript:

  JetQuotRec2 s (padSeq3 (w0At  m s))
  JetQuotRec2 s (padSeq3 (wp2At m s))
  JetQuotRec2 s (padSeq3 (wp3At m s))
-/

axiom rec2_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (w0At m s))

axiom rec2_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp2At m s))

axiom rec2_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp3At m s))

/-- Packaged recurrence payload (becomes theorem-level when the three axioms are discharged). -/
theorem xiJetQuotRec2AtOrder_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s :=
  ⟨ rec2_w0At_trueAnalytic (m := m) (s := s),
    rec2_wp2At_trueAnalytic (m := m) (s := s),
    rec2_wp3At_trueAnalytic (m := m) (s := s) ⟩

/-- True-analytic Rec2 provider instance (currently staged via the three axioms above). -/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := xiJetQuotRec2AtOrder_fromTrueAnalytic

end XiPacket
end Targets
end Hyperlocal
