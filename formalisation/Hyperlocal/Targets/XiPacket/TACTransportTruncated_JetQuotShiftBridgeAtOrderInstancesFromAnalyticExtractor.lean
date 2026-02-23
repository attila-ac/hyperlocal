/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridgeAtOrderInstancesFromAnalyticExtractor.lean

  Provide JetQuotShiftBridge3AtOrder instances for the three canonical windows
  using ONLY the minimal window-equality axiom surface.

  Design:
  * Non-cycle-safe (imports the analytic axiom layer),
    but keeps the semantic cliff minimal.
  * These instances allow cycle-safe downstream code to consume the bridge class
    without ever mentioning the analytic endpoint structures.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-- Instance for `w0At`: from `JetQuotRec2` we can view it as an order-m jet at `z_w0At`. -/
instance jetQuotShiftBridge3AtOrder_w0At
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_w0At s) (w0At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw :
        w0At m s = xiJet3AtOrder m (z_w0At s) :=
      (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder
    simpa [IsJet3AtOrder, hw] using
      (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_w0At s))

/-- Instance for `wp2At`. -/
instance jetQuotShiftBridge3AtOrder_wp2At
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_wp2At s) (wp2At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw :
        wp2At m s = xiJet3AtOrder m (z_wp2At s) :=
      (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder
    simpa [IsJet3AtOrder, hw] using
      (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp2At s))

/-- Instance for `wp3At`. -/
instance jetQuotShiftBridge3AtOrder_wp3At
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotShiftBridge3AtOrder m s (z_wp3At s) (wp3At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw :
        wp3At m s = xiJet3AtOrder m (z_wp3At s) :=
      (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder
    simpa [IsJet3AtOrder, hw] using
      (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp3At s))

end TAC

end XiPacket
end Targets
end Hyperlocal
