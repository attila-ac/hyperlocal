/-
  Strip-only theorem provider for the Row0 heart.

  Goal: provide `xiJetQuotRow0AtOrderHeartOut_strip` WITHOUT importing the global
  nondegeneracy module/axiom `a0_ne_zero`.

  This file is non-cycle-safe (imports the analytic extractor endpoint).
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Strip-specialised heart output discharged from the analytic extractor Rec2 triple,
using `a0_ne_zero_of_strip` (no global axiom import).
-/
theorem xiJetQuotRow0AtOrderHeartOut_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiJetQuotRow0AtOrderHeartOut m (s : OffSeed Xi) := by
  classical

  have Hrec2 :
      JetQuotRec2 (s : OffSeed Xi) (padSeq3 (w0At m (s : OffSeed Xi))) ∧
      JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp2At m (s : OffSeed Xi))) ∧
      JetQuotRec2 (s : OffSeed Xi) (padSeq3 (wp3At m (s : OffSeed Xi))) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := (s : OffSeed Xi))

  have ha0 : a0 (s : OffSeed Xi) ≠ (0 : ℂ) := by
    simpa [a0] using a0_ne_zero_of_strip (s := s)

  have Hw0 : (w0At m (s : OffSeed Xi)) 0 = 0 ∧
             (w0At m (s : OffSeed Xi)) 1 = 0 ∧
             (w0At m (s : OffSeed Xi)) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := (s : OffSeed Xi)) (w := w0At m (s : OffSeed Xi)) Hrec2.1 ha0

  have Hwp2 : (wp2At m (s : OffSeed Xi)) 0 = 0 ∧
              (wp2At m (s : OffSeed Xi)) 1 = 0 ∧
              (wp2At m (s : OffSeed Xi)) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := (s : OffSeed Xi)) (w := wp2At m (s : OffSeed Xi)) Hrec2.2.1 ha0

  have Hwp3 : (wp3At m (s : OffSeed Xi)) 0 = 0 ∧
              (wp3At m (s : OffSeed Xi)) 1 = 0 ∧
              (wp3At m (s : OffSeed Xi)) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := (s : OffSeed Xi)) (w := wp3At m (s : OffSeed Xi)) Hrec2.2.2 ha0

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
