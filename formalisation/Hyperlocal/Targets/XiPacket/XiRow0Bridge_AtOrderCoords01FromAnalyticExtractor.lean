/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalyticExtractor.lean

  Extractor-side theorem (NOT cycle-safe):

  From the analytic extractor’s Rec2 triple at order m, derive the
  coordinate vanishings w0=0 and w1=0 for each of the three AtOrder windows.

  Uses:
  * xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor
  * coords_eq_zero_of_rec2_padSeq3 (pure algebra)
  * a0_ne_zero (minimal nondegeneracy boundary)

  This file is meant to be the theorem-level replacement for the axiom in:
    XiRow0Bridge_AtOrderCoords01FromAnalytic.lean
  once you can connect DAG-wise without cycles.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Theorem-level coords bundle from the analytic extractor Rec2 triple.
-/
theorem xiAtOrderCoords01Out_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    XiAtOrderCoords01Out m s := by
  -- get the Rec2 triple from the analytic extractor
  have Hrec2 :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)

  have ha0 : a0 s ≠ (0 : ℂ) := by
    -- `a0` is abbrev in XiRow0Bridge_Rec2PadSeq3ToCoords: a0 s = JetQuotOp.aRk1 s 0
    simpa [a0] using a0_ne_zero (s := s)

  -- window w0At
  have Hw0 : (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (w0At m s)) Hrec2.1 ha0

  -- window wp2At
  have Hwp2 : (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (wp2At m s)) Hrec2.2.1 ha0

  -- window wp3At
  have Hwp3 : (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := (wp3At m s)) Hrec2.2.2 ha0

  -- package only 0/1 coords
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
