/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticSource.lean

  Interim "true-analytic source" layer for the Rec2AtOrder provider.

  Final intent:
  * Replace the proofs in this file by genuinely analytic lemmas from FE/RC/factorisation
    (no extractor, no Row012 upstream).

  Current state (2026-02-22):
  * We eliminate the local axioms in `...ProviderTrueAnalytic.lean` by sourcing the
    three padded-sequence recurrences from the extractor-free Path–A Row012 upstream chain.
  * This makes the Rec2 provider theorem-level and extractor-free today.

  When you later prove the recurrences directly from the FE/RC/manuscript stack,
  only this file needs to change.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## The three padded-sequence recurrences

These are the exact targets expected by `...ProviderTrueAnalytic.lean`.

Today they are derived from the extractor-free Row012 upstream chain.
Replace these proofs one-by-one by genuine FE/RC/factorisation theorems when available.
-/

theorem rec2_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (w0At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)).h_w0At

theorem rec2_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)).h_wp2At

theorem rec2_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  exact (xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)).h_wp3At

end XiPacket
end Targets
end Hyperlocal
