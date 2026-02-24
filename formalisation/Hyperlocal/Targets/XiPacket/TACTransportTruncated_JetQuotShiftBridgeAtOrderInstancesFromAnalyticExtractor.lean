/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridgeAtOrderInstancesFromAnalyticExtractor.lean

  Step 4 refactor (Option B / quotient jets):
  Instances depend on `[XiJetWindowEqAtOrderQuotProvider]` and produce
  `JetQuotShiftBridge3AtOrderQuot`, i.e. quotient jets of `routeA_G s`.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-
  Center alignment (only needed because `z_w0At` in the transport layer is not
  definitional `s.ρ` in your snapshot).
-/
private lemma z_w0At_eq_rho (s : OffSeed Xi) : z_w0At s = s.ρ := by
  -- keep exactly the same simp proof you used earlier
  refine Complex.ext ?_ ?_
  · simp [z_w0At, XiTransport.delta, sc, t, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm]
  · simp [z_w0At, XiTransport.delta, sc, t, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm]

/-- Instance for `w0At` (quotient bridge). -/
instance jetQuotShiftBridge3AtOrderQuot_w0At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_w0At s) (w0At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw_rho :
        w0At m s = jet3 (routeA_G s) (s.ρ) :=
      (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).w0At_eq
    have hw :
        w0At m s = jet3 (routeA_G s) (z_w0At s) := by
      simpa [z_w0At_eq_rho (s := s)] using hw_rho
    -- Goal is `IsJet3At (routeA_G s) (z_w0At s) (w0At m s)` (definally via IsJet3AtOrderQuot)
    simpa [IsJet3AtOrderQuot, hw] using
      (isJet3At_jet3 (G := routeA_G s) (z := z_w0At s))

/-- Instance for `wp2At` (quotient bridge). -/
instance jetQuotShiftBridge3AtOrderQuot_wp2At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_wp2At s) (wp2At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw :
        wp2At m s = jet3 (routeA_G s) (z_wp2At s) := by
      -- in the transport layer, `z_wp2At` is definitional `star s.ρ` in your original file,
      -- but to be snapshot-robust we just `simpa` it through the provider equality
      simpa [z_wp2At] using
        (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).wp2At_eq
    simpa [IsJet3AtOrderQuot, hw] using
      (isJet3At_jet3 (G := routeA_G s) (z := z_wp2At s))

/-- Instance for `wp3At` (quotient bridge). -/
instance jetQuotShiftBridge3AtOrderQuot_wp3At
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderQuotProvider] :
    JetQuotShiftBridge3AtOrderQuot m s (z_wp3At s) (wp3At m s) where
  jet_of_rec2 := by
    intro _Hrec2
    have hw :
        wp3At m s = jet3 (routeA_G s) (z_wp3At s) := by
      simpa [z_wp3At] using
        (XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot (m := m) (s := s)).wp3At_eq
    simpa [IsJet3AtOrderQuot, hw] using
      (isJet3At_jet3 (G := routeA_G s) (z := z_wp3At s))

end TAC

end XiPacket
end Targets
end Hyperlocal
