/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrencesStrict.lean

  STRICT (non-typeclass, non-recursive) theorem layer for Task A.

  Goal:
    expose the three Rec2 facts needed for the canonical windows
      `w0At`, `wp2At`, `wp3At`
    as plain theorems (no class projections), so that the landing pad
    `XiToeplitzRecurrenceJetQuotientRec2AtOrderTrueAnalytic.lean`
    can install `[XiJetQuotRec2AtOrderTrueAnalytic]` without looping.

  IMPORTANT (Task A “proper”):
  This file intentionally avoids importing the extractor chain.
  It derives Rec2 from the true-analytic JetConvolution → Row012 → Rec2 provider pipeline.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution

-- Provide `XiJetConvolutionAtRevAtOrderTrueAnalytic` from tail345 (theorem-level).
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge

-- Make the tail345 instance available in a robust way.
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ManuscriptFromSigmaAndRow012

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## Strict Rec2 theorems (plain, non-typeclass)

These are the only three facts Task A needs.
They are obtained from the already-wired provider
`[XiJetQuotRec2AtOrderProvider]` (which itself is built from the
true-analytic JetConvolution/Row012 pipeline).
-/

/-- Plain theorem (non-typeclass): recurrence for `w0At`. -/
theorem xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  simpa using (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_w0At

/-- Plain theorem (non-typeclass): recurrence for `wp2At`. -/
theorem xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  simpa using (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_wp2At

/-- Plain theorem (non-typeclass): recurrence for `wp3At`. -/
theorem xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  simpa using (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_wp3At

end XiPacket
end Targets
end Hyperlocal
