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
  This file intentionally avoids the extractor chain.
  It now consumes the TRUE-ANALYTIC ROOT import surface, whose tail345 payload
  is supplied by the heart+coords corridor, rather than the older
  sigma+row012 manuscript cone.

  2026-03-11 downstream retarget:
  * remove the old direct dependency on
      `XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ManuscriptFromSigmaAndRow012`
  * import the clean Rec2 true-analytic root instead
  * keep the strict theorem bodies unchanged
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012UpstreamTrueAnalytic

/-
  Downstream consumer retarget:

  This root already wires
    Tail345 manuscript payload (from heart+coords)
      ⇒ JetConvolutionAtRev discharge
      ⇒ Row012ConvolutionAtRev
      ⇒ Row012Upstream
      ⇒ Rec2 true-analytic provider surface

  So this strict theorem layer should consume that root, not the older
  sigma+row012 manuscript producer directly.
-/
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot

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
`[XiJetQuotRec2AtOrderProvider]` living in the true-analytic root cone.
-/

/-- Plain theorem (non-typeclass): recurrence for `w0At`. -/
theorem xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_w0At

/-- Plain theorem (non-typeclass): recurrence for `wp2At`. -/
theorem xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_wp2At

/-- Plain theorem (non-typeclass): recurrence for `wp3At`. -/
theorem xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  exact (xiJetQuotRec2AtOrder_provided (m := m) (s := s)).h_wp3At

end XiPacket
end Targets
end Hyperlocal
