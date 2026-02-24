/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridgeAtOrderInstancesFromAnalyticExtractor.lean

  Pure plumbing (quotient arm):

  Given `[XiJetWindowEqAtOrderQuotProvider]`, install the three instances

    JetQuotShiftBridge3AtOrderQuot m s (z_w0At  s) (w0At  m s)
    JetQuotShiftBridge3AtOrderQuot m s (z_wp2At s) (wp2At m s)
    JetQuotShiftBridge3AtOrderQuot m s (z_wp3At s) (wp3At m s)

  at the canonical quotient anchors `z_w0At/z_wp2At/z_wp3At`.

  Snapshot-robust:
  - `z_*` are defined in `XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider.lean` (namespace `...XiPacket.TAC`)
  - `XiJetWindowEqAtOrderQuotProvider` and `isJet3At_jet3` are provided by
    `XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean` (same namespace).
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

@[instance 1000]
instance jetQuotShiftBridge3AtOrderQuot_w0At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_w0At s) (w0At m s) where
  jet_of_rec2 := by
    intro _Hrec
    have hw :
        w0At m s = jet3 (routeA_G s) (z_w0At s) :=
      (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).w0At_eq
    -- `isJet3At_jet3` proves `IsJet3At G z (jet3 G z)` with no recurrence needed.
    have hj :
        IsJet3At (routeA_G s) (z_w0At s) (jet3 (routeA_G s) (z_w0At s)) := by
      simpa using (isJet3At_jet3 (G := routeA_G s) (z := z_w0At s))
    simpa [IsJet3AtOrderQuot, hw] using hj

@[instance 1000]
instance jetQuotShiftBridge3AtOrderQuot_wp2At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_wp2At s) (wp2At m s) where
  jet_of_rec2 := by
    intro _Hrec
    have hw :
        wp2At m s = jet3 (routeA_G s) (z_wp2At s) :=
      (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).wp2At_eq
    have hj :
        IsJet3At (routeA_G s) (z_wp2At s) (jet3 (routeA_G s) (z_wp2At s)) := by
      simpa using (isJet3At_jet3 (G := routeA_G s) (z := z_wp2At s))
    simpa [IsJet3AtOrderQuot, hw] using hj

@[instance 1000]
instance jetQuotShiftBridge3AtOrderQuot_wp3At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_wp3At s) (wp3At m s) where
  jet_of_rec2 := by
    intro _Hrec
    have hw :
        wp3At m s = jet3 (routeA_G s) (z_wp3At s) :=
      (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).wp3At_eq
    have hj :
        IsJet3At (routeA_G s) (z_wp3At s) (jet3 (routeA_G s) (z_wp3At s)) := by
      simpa using (isJet3At_jet3 (G := routeA_G s) (z := z_wp3At s))
    simpa [IsJet3AtOrderQuot, hw] using hj

end TAC

end XiPacket
end Targets
end Hyperlocal
