/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetQuotShiftBridgeInstancesFromAnalyticExtractor.lean

  Step B (non-cycle-safe discharge layer, theorem-level *given* the analytic-jet axiom package):

  We install instances of `TAC.JetQuotShiftBridge3` for:
    * w0At m s
    * wp2At m s
    * wp3At m s

  These instances are now *sorriless* because the only semantic cliff is
  concentrated in the single primitive endpoint:

    `xiJetQuotRow012AtOrder_analyticJet`
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor
import Mathlib.Analysis.Calculus.Deriv.Basic
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
  They are already defined in `...AnalyticJetAxiom.lean` in this same namespace `TAC`.
-/

/-- Step-B instance for `w0At`. -/
instance jetQuotShiftBridge3_w0At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3 m s (z_w0At s) (w0At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_w0At

/-- Step-B instance for `wp2At`. -/
instance jetQuotShiftBridge3_wp2At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3 m s (z_wp2At s) (wp2At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_wp2At

/-- Step-B instance for `wp3At`. -/
instance jetQuotShiftBridge3_wp3At (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3 m s (z_wp3At s) (wp3At m s) where
  jet_of_rec2 := by
    intro _Hrec
    exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_wp3At

/--
Convenience lemma: the three Jet3 facts.

(Here we show them in the “extractor style” too, to keep usage patterns consistent.)
-/
theorem isJet3At_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3At Xi (z_w0At s) (w0At m s) ∧
    IsJet3At Xi (z_wp2At s) (wp2At m s) ∧
    IsJet3At Xi (z_wp3At s) (wp3At m s) := by
  classical
  have _Hrec2 :=
    xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s)
  -- the recurrences are unused: the semantic meaning is concentrated in the analytic-jet endpoint
  refine ⟨?_, ?_, ?_⟩
  · exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_w0At
  · exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_wp2At
  · exact (xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)).jet_wp3At

end TAC

end XiPacket
end Targets
end Hyperlocal
