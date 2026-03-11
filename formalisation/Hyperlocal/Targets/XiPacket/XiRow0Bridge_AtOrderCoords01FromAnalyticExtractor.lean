/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalyticExtractor.lean

  Extractor-side derivation of the AtOrder coordinate bundle (general branch).

  This file is **not** cycle-safe: it imports the analytic extractor endpoint.

  IMPORTANT:
  Any division by `JetQuotOp.aRk1 s 0` must assume it explicitly.
  Therefore this theorem requires `[A0Nonzero s]`.

  Graph discipline:
  * this file must remain on the historical extractor corridor
  * it may consume the installed sigma surface
  * it may consume the DAG-clean coords fallback surface
  * it must NOT switch to the theorem-side packaged extractor endpoint,
    because that endpoint itself requires `[XiAtOrderCoords01Provider]`,
    which would make this file circular
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Extractor-side discharged coords bundle from the analytic extractor (general `OffSeed Xi`). -/
theorem xiAtOrderCoords01Out_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiAtOrderCoords01Out m s := by
  classical

  have Hrec2 :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)

  have ha0 : JetQuotOp.aRk1 s 0 ≠ (0 : ℂ) :=
    A0Nonzero.a0_ne_zero (s := s)

  have Hw0 : (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := w0At m s) Hrec2.1 ha0

  have Hwp2 : (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp2At m s) Hrec2.2.1 ha0

  have Hwp3 : (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp3At m s) Hrec2.2.2 ha0

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
