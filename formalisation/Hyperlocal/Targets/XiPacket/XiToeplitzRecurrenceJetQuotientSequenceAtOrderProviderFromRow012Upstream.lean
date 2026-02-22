/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream.lean

  Extractor-free glue:
  provide the Rec2AtOrder provider instance by deriving the recurrence payload
  from the *Row012 Prop* upstream endpoint.

  Pipeline used:
    Row012 Prop upstream (Path-A semantic chain)
      ⇒ (Prop ⇒ Type) Row012 packaging
      ⇒ XiJetQuotRec2AtOrder m s
      ⇒ instance : XiJetQuotRec2AtOrderProvider

  IMPORTANT:
  * This file does NOT import extractor-facing modules.
  * This file does NOT import the Row012 analytic-axiom endpoint module
      XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean
    and does not depend on it.
  * It *does* depend on your Row012 upstream proof provider, which in turn
    currently installs DAG-clean provider instances (sigma/coords). That is the
    intended remaining analytic surface anyway.

  Usage:
  * If you import this file, you do not need
      XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderAxiom.lean
    nor the extractor-provider instance for Rec2.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

-- Row012 Prop upstream endpoint (Path-A semantic chain; currently uses provider instances)
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream

-- Cycle-safe bridges:
--   Prop Row012 ⇒ Type Row012
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromPropBridge
--   Type Row012 ⇒ Rec2AtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Extractor-free recurrence payload derived from the Row012 Prop upstream endpoint.
-/
theorem xiJetQuotRec2AtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical

  -- 1) Row012 Prop payload (already derived by your upstream chain)
  have Hrow012Prop : XiJetQuotRow012PropAtOrder m s :=
    xiJetQuotRow012PropAtOrder_analytic_upstream (m := m) (s := s)

  -- 2) Prop ⇒ Type (cycle-safe packaging bridge)
  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_of_row012PropAtOrder (m := m) (s := s) Hrow012Prop

  -- 3) Type Row012 ⇒ Rec2 bundle (pure algebra bridge; in Row012ToSequenceBridge)
  exact xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

/-- Provider instance derived from Row012 upstream (extractor-free). -/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := xiJetQuotRec2AtOrder_fromRow012Upstream

end XiPacket
end Targets
end Hyperlocal
