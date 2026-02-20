/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientAnalyticSequenceRec2AtOrder.lean

  Purpose:
  * Define the canonical ℕ-sequences `J₀, J₂, J₃` attached to the three AtOrder windows
    (currently as `padSeq3 (w0At/wp2At/wp3At)`).
  * Expose the recurrence as a single theorem `JetQuotRec2 s (J?At m s)` by projection from
    `xiJetQuotRec2AtOrder_fromRecurrenceA`.

  This is the exact theorem shape the future “true analytic recurrence extractor” should
  eventually prove directly (without passing through the manuscript-facing axiom).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Canonical (current) “analytic-sequence stand-in”: padded jet-quotient window `w0At`. -/
def J0At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  padSeq3 (w0At m s)

/-- Canonical (current) padded prime window `wp2At`. -/
def J2At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  padSeq3 (wp2At m s)

/-- Canonical (current) padded prime window `wp3At`. -/
def J3At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  padSeq3 (wp3At m s)

@[simp] lemma J0At_def (m : ℕ) (s : OffSeed Xi) : J0At m s = padSeq3 (w0At m s) := rfl
@[simp] lemma J2At_def (m : ℕ) (s : OffSeed Xi) : J2At m s = padSeq3 (wp2At m s) := rfl
@[simp] lemma J3At_def (m : ℕ) (s : OffSeed Xi) : J3At m s = padSeq3 (wp3At m s) := rfl

/--
**Current theorem-level recurrence** on the canonical sequence `J0At`.

NOTE: This is theorem-level, but still inherits the remaining manuscript-facing axiom
indirectly via `xiJetQuotRec2AtOrder_fromRecurrenceA`.
-/
theorem jetQuotRec2_J0At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (J0At m s) := by
  simpa [J0At] using (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_w0At

/-- Same, for `J2At`. -/
theorem jetQuotRec2_J2At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (J2At m s) := by
  simpa [J2At] using (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_wp2At

/-- Same, for `J3At`. -/
theorem jetQuotRec2_J3At_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : JetQuotRec2 s (J3At m s) := by
  simpa [J3At] using (xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)).h_wp3At

end XiPacket
end Targets
end Hyperlocal
