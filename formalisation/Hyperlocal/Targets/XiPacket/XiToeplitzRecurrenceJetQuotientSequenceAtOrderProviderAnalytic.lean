/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderAnalytic.lean

  Historical surface: Rec2 facts for the order-`m` Toeplitz/jet-quotient sequence.

  PREVIOUSLY:
    This file axiom-staged three Rec2 facts
      `rec2_w0At_analytic`, `rec2_wp2At_analytic`, `rec2_wp3At_analytic`.

  NOW (theorem-level):
    We obtain these facts from the provider bundle
      `XiJetQuotRec2AtOrderProvider`
    installed by
      `XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor`.

  Policy:
    * keep the historical theorem names (they appear in `#print axioms` cones)
    * introduce no new axioms
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-!
  These three are exported names that downstream expects.
  They are now theorems (not axioms), derived from the provider bundle.
-/

/-- Rec2 for the padded order-`m` transported central jet window `w0At m s` (theorem-level). -/
theorem rec2_w0At_analytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  -- Provided by the instance `XiJetQuotRec2AtOrderProvider`.
  simpa using (XiJetQuotRec2AtOrder.h_w0At (xiJetQuotRec2AtOrder_provided (m := m) (s := s)))

/-- Rec2 for the padded order-`m` transported payload window `wp2At m s` (theorem-level). -/
theorem rec2_wp2At_analytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  simpa using (XiJetQuotRec2AtOrder.h_wp2At (xiJetQuotRec2AtOrder_provided (m := m) (s := s)))

/-- Rec2 for the padded order-`m` transported payload window `wp3At m s` (theorem-level). -/
theorem rec2_wp3At_analytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  simpa using (XiJetQuotRec2AtOrder.h_wp3At (xiJetQuotRec2AtOrder_provided (m := m) (s := s)))

end XiPacket
end Targets
end Hyperlocal
