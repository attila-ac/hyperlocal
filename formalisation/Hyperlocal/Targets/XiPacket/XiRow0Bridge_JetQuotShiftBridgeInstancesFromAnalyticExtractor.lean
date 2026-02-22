/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetQuotShiftBridgeInstancesFromAnalyticExtractor.lean

  Step B (non-cycle-safe discharge layer, theorem-level *given* the analytic-jet axiom package):

  We install instances of `TAC.JetQuotShiftBridge3AtOrder` for:
    * w0At m s
    * wp2At m s
    * wp3At m s

  These instances are now *sorriless* because the only semantic cliff is
  concentrated in the single primitive endpoint:

    `xiJetQuotRow012AtOrder_analyticJet`
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

/-
  IMPORTANT:
  Do NOT redeclare `z_w0At/z_wp2At/z_wp3At` here.
  They are defined in `...Row012AtOrderAnalyticJetAxiom.lean` in this same namespace `TAC`.
-/

/-- Step-B instance for `w0At` (order-m jet). -/
instance jetQuotShiftBridge3AtOrder_w0At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_w0At s) (w0At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_w0At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))

/-- Step-B instance for `wp2At` (order-m jet). -/
instance jetQuotShiftBridge3AtOrder_wp2At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_wp2At s) (wp2At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp2At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))

/-- Step-B instance for `wp3At` (order-m jet). -/
instance jetQuotShiftBridge3AtOrder_wp3At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_wp3At s) (wp3At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp3At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))

/--
Convenience lemma: the three order-m Jet3 facts.

(Shown in the “extractor style” too, to keep usage patterns consistent.)
-/
theorem isJet3AtOrder_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) ∧
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) ∧
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  classical
  have _Hrec2 :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)
  refine ⟨?_, ?_, ?_⟩
  · exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_w0At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))
  · exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp2At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))
  · exact (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp3At
      (m := m) (s := s) (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))

end TAC

end XiPacket
end Targets
end Hyperlocal
