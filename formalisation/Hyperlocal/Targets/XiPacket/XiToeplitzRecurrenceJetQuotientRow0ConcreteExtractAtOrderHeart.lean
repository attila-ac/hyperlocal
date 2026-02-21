/-
  General heart theorem provider (stable API for Frontier/Wrapper).

  This file may still import the global nondegeneracy boundary `a0_ne_zero`
  so existing downstream modules (expecting `OffSeed Xi`) keep compiling.

  Strip branch should NOT import this file; it should import:
    `...HeartFromAnalyticStrip.lean`
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Stable heart output: for any `OffSeed Xi` (used by Frontier). -/
theorem xiJetQuotRow0AtOrderHeartOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderHeartOut m s := by
  classical

  have Hrec2 :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)

  have ha0 : a0 s ≠ (0 : ℂ) := by
    simpa [a0] using a0_ne_zero (s := s)

  have Hw0 : (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := w0At m s) Hrec2.1 ha0
  have Hwp2 : (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp2At m s) Hrec2.2.1 ha0
  have Hwp3 : (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp3At m s) Hrec2.2.2 ha0

  refine ⟨?_, ?_, ?_⟩
  · rcases Hw0 with ⟨hw0, hw1, hw2⟩
    simp [row0Sigma, hw0, hw1, hw2]
  · rcases Hwp2 with ⟨hw0, hw1, hw2⟩
    simp [row0Sigma, hw0, hw1, hw2]
  · rcases Hwp3 with ⟨hw0, hw1, hw2⟩
    simp [row0Sigma, hw0, hw1, hw2]

end XiPacket
end Targets
end Hyperlocal
