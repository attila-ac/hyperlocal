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

theorem xiAtOrderCoords01Out_fromAnalyticExtractor
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m s := by
  have Hrec2 :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)

  have ha0 : a0 s ≠ (0 : ℂ) := by
    simpa [a0] using a0_ne_zero_of_strip (s := s)

  have Hw0 : (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (w0At m s)) Hrec2.1 ha0
  have Hwp2 : (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (wp2At m s)) Hrec2.2.1 ha0
  have Hwp3 : (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (wp3At m s)) Hrec2.2.2 ha0

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
