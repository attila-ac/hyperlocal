/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartFromAnalyticStrip.lean

  Strip-only theorem provider for the Row0 heart.

  Goal: provide `xiJetQuotRow0AtOrderHeartOut_strip` without importing the
  ambient coords01 fallback installer.

  2026-03-12 follow-up refactor:
  * consume the theorem-clean strip extractor
  * expose the honest true-analytic gate explicitly
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractorFromRec2TrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

theorem xiJetQuotRow0AtOrderHeartOut_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0AtOrderHeartOut m (s : OffSeed Xi) := by
  classical

  let s0 : OffSeed Xi := (s : OffSeed Xi)

  have Hrec2 :
      JetQuotRec2 s0 (padSeq3 (w0At m s0)) ∧
      JetQuotRec2 s0 (padSeq3 (wp2At m s0)) ∧
      JetQuotRec2 s0 (padSeq3 (wp3At m s0)) := by
    simpa [s0] using
      (xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor_fromRec2TrueAnalytic_strip
        (m := m) (s := s))

  have ha0 : a0 s0 ≠ (0 : ℂ) := by
    simpa [a0, s0] using (a0_ne_zero_of_strip (s := s))

  have Hw0 : (w0At m s0) 0 = 0 ∧
             (w0At m s0) 1 = 0 ∧
             (w0At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := w0At m s0) Hrec2.1 ha0

  have Hwp2 : (wp2At m s0) 0 = 0 ∧
              (wp2At m s0) 1 = 0 ∧
              (wp2At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := wp2At m s0) Hrec2.2.1 ha0

  have Hwp3 : (wp3At m s0) 0 = 0 ∧
              (wp3At m s0) 1 = 0 ∧
              (wp3At m s0) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s0) (w := wp3At m s0) Hrec2.2.2 ha0

  refine ⟨?_, ?_, ?_⟩
  · rcases Hw0 with ⟨hw0, hw1, hw2⟩
    dsimp [s0] at hw0 hw1 hw2 ⊢
    simp [row0Sigma, hw0, hw1, hw2]
  · rcases Hwp2 with ⟨hw0, hw1, hw2⟩
    dsimp [s0] at hw0 hw1 hw2 ⊢
    simp [row0Sigma, hw0, hw1, hw2]
  · rcases Hwp3 with ⟨hw0, hw1, hw2⟩
    dsimp [s0] at hw0 hw1 hw2 ⊢
    simp [row0Sigma, hw0, hw1, hw2]

end XiPacket
end Targets
end Hyperlocal
