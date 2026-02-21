/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalyticExtractorStrip.lean

  Extractor-side derivation of the AtOrder coordinate bundle (strip branch).

  This file is **not** cycle-safe: it imports the analytic extractor endpoint.
  It is the strip-specialised version that avoids the global axiom
  `a0_ne_zero` by using the theorem `a0_ne_zero_of_strip`.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Extractor-side discharged coords bundle from the analytic extractor (strip-specialised). -/
theorem xiAtOrderCoords01Out_fromAnalyticExtractor_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m (s : OffSeed Xi) := by
  set s0 : OffSeed Xi := (s : OffSeed Xi)

  have Hrec2 :
      JetQuotRec2 s0 (padSeq3 (w0At m s0)) ∧
      JetQuotRec2 s0 (padSeq3 (wp2At m s0)) ∧
      JetQuotRec2 s0 (padSeq3 (wp3At m s0)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s0)

  have ha0 : a0 s0 ≠ (0 : ℂ) := by
    simpa [s0, a0] using (a0_ne_zero_of_strip (s := s))

  have Hw0 : (w0At m s0) 0 = 0 ∧ (w0At m s0) 1 = 0 ∧ (w0At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := (w0At m s0)) Hrec2.1 ha0
  have Hwp2 : (wp2At m s0) 0 = 0 ∧ (wp2At m s0) 1 = 0 ∧ (wp2At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := (wp2At m s0)) Hrec2.2.1 ha0
  have Hwp3 : (wp3At m s0) 0 = 0 ∧ (wp3At m s0) 1 = 0 ∧ (wp3At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := (wp3At m s0)) Hrec2.2.2 ha0

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Hw0.1
  · exact Hw0.2.1
  · exact Hwp2.1
  · exact Hwp2.2.1
  · exact Hwp3.1
  · exact Hwp3.2.1

end XiPacket
end Targets
end Hyperlocal
