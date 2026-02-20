/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrences.lean

  TARGET:
  Produce the three single-statement recurrences *directly from analytic inputs*:

    JetQuotRec2 s (padSeq3 (w0At m s))
    JetQuotRec2 s (padSeq3 (wp2At m s))
    JetQuotRec2 s (padSeq3 (wp3At m s))

  Architecture (clean):
    * NO axioms in this endpoint file.
    * It re-exports the theorem proved in the extractor file.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Analytic endpoint: the three padded-sequence JetQuot recurrences at order `m`.
-/
theorem xiJetQuotRec2_padSeq3_triple_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  simpa using
    (xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s))

theorem xiJetQuotRec2_padSeq3_w0At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) :=
  (xiJetQuotRec2_padSeq3_triple_fromAnalytic (m := m) (s := s)).1

theorem xiJetQuotRec2_padSeq3_wp2At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp2At m s)) :=
  (xiJetQuotRec2_padSeq3_triple_fromAnalytic (m := m) (s := s)).2.1

theorem xiJetQuotRec2_padSeq3_wp3At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (wp3At m s)) :=
  (xiJetQuotRec2_padSeq3_triple_fromAnalytic (m := m) (s := s)).2.2

end XiPacket
end Targets
end Hyperlocal
