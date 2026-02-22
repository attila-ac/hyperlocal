/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderAnalytic.lean

  Analytic-only landing pad for the Rec2AtOrder provider instance (FULL R0).

  Goal: replace the remaining Rec2 provider axiom instance by a theorem-level instance:
    instance : XiJetQuotRec2AtOrderProvider

  DAG contract:
  * Only "true analytic" imports (FE/RC/factorisation/jet identities / manuscript recurrences).
  * MUST NOT import extractor-facing modules.

  Today this file contains three local axioms (one per AtOrder window recurrence)
  to keep the API stable. Replace them one-by-one by real analytic theorems, then
  delete the axioms.

  Once this instance is theorem-level, you can switch the public surface import from:
    ...ProviderFromAnalyticExtractor
  to:
    ...ProviderAnalytic
  without touching any downstream consumer.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## True analytic surface (3 subgoals)

These are exactly the three recurrence facts that must be proven from the manuscript/analytic layer:

  JetQuotRec2 s (padSeq3 (w0At  m s))
  JetQuotRec2 s (padSeq3 (wp2At m s))
  JetQuotRec2 s (padSeq3 (wp3At m s))
-/

axiom rec2_w0At_analytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (w0At m s))

axiom rec2_wp2At_analytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp2At m s))

axiom rec2_wp3At_analytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp3At m s))

/-- Theorem-level packaged recurrence payload (once axioms above are discharged, this is too). -/
theorem xiJetQuotRec2AtOrder_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s :=
  ⟨ rec2_w0At_analytic (m := m) (s := s),
    rec2_wp2At_analytic (m := m) (s := s),
    rec2_wp3At_analytic (m := m) (s := s) ⟩

/-- Theorem-level analytic Rec2 provider instance (currently staged via the three axioms above). -/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := xiJetQuotRec2AtOrder_fromAnalytic

end XiPacket
end Targets
end Hyperlocal
