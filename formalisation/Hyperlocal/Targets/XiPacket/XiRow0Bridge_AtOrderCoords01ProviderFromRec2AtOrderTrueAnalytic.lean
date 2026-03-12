/-
  Coords01-at-order output derived from the TRUE-ANALYTIC Rec2-at-order route.

  2026-03-12 surgical retarget:
  * remove the hidden dependency on `A0NonzeroBoundaryFromAxiom`
  * keep the existing strict Rec2 padSeq3 proof body
  * derive `a0 ≠ 0` locally from the strip nondegeneracy theorem
  * strengthen the theorem gate to the honest true-analytic surface
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrencesStrict

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

theorem xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s := by
  classical
  letI : XiJetQuotRec2AtOrderProvider := inferInstance

  rcases offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : (ss : OffSeed Xi) = s := by
    rfl

  have ha0 : JetQuotOp.aRk1 s 0 ≠ 0 := by
    simpa [hs] using (a0_ne_zero_of_strip (s := ss))

  have hw0 :
      (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := w0At m s)
      (ha0 := ha0)
      (xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict (m := m) (s := s))

  have hwp2 :
      (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp2At m s)
      (ha0 := ha0)
      (xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict (m := m) (s := s))

  have hwp3 :
      (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3 (s := s) (w := wp3At m s)
      (ha0 := ha0)
      (xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict (m := m) (s := s))

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw0.1
  · exact hw0.2.1
  · exact hwp2.1
  · exact hwp2.2.1
  · exact hwp3.1
  · exact hwp3.2.1

end XiPacket
end Targets
end Hyperlocal
