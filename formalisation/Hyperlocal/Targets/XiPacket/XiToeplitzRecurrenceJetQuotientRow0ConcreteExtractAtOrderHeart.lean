/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Heart contract (sigma-only).

  NOTE (2026-02-21):
  This file is no longer “cycle-safe”: it now DISCHARGES the former heart axiom from the
  analytic extractor Rec2 triple (and the nondegeneracy axiom `a0_ne_zero`).

  Net effect:
  - removes the previous axiom `xiJetQuotRow0AtOrderHeartOut`
  - provides theorem-level `row0Sigma = 0` for the three AtOrder windows.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

-- Non-cycle-safe discharge inputs
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

/--
Heart output: the scalar Row0 goals (row0Sigma = 0) for the three AtOrder windows.
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

/--
Theorem-level heart output: discharged from the analytic extractor Rec2 triple.

Depends on:
* the upstream analytic row012 landing axiom `xiJetQuotRow012AtOrder_analytic`
  (via the analytic extractor endpoint),
* the nondegeneracy axiom `a0_ne_zero`.
-/
theorem xiJetQuotRow0AtOrderHeartOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderHeartOut m s := by
  classical

  have Hrec2 :
      JetQuotRec2 s (padSeq3 (w0At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
      JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)

  have ha0 : a0 s ≠ (0 : ℂ) := by
    -- `a0` is abbrev in XiRow0Bridge_Rec2PadSeq3ToCoords
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
