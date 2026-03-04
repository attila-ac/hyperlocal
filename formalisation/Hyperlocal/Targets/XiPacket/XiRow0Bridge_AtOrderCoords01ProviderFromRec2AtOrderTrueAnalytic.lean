/-
  Coords01-at-order output derived from the TRUE-ANALYTIC Rec2-at-order route,
  plus a single nondegeneracy boundary axiom (A0NonzeroBoundary).

  This is extractor-free: it stays on the true-analytic payload spine.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRec2AtOrderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

theorem xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s := by
  classical

  -- semantic cliff you said you're okay with:
  have ha0 : JetQuotOp.aRk1 s 0 ≠ 0 :=
    (A0Nonzero.a0_ne_zero (s := s))

  -- w0At
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

  -- Coords01 wants only coordinates 0 and 1 at each point.
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
