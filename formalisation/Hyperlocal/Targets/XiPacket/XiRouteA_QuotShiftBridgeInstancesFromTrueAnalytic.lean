/-
  Hyperlocal/Targets/XiPacket/XiRouteA_QuotShiftBridgeInstancesFromTrueAnalytic.lean

  One-stop “instance glue” for the Route–A / quotient arm.

  IMPORTANT (cycle-safety):
  We do NOT try to `infer_instance` a global `XiJetWindowEqAtOrderQuotProvider` here.
  That would be circular unless you already have a non-circular source of
  `XiJetWindowIsJetAtOrderQuotProvider` (or a direct Eq-provider instance).

  Instead, this file is purely an *installer*:
    assuming `[XiJetWindowEqAtOrderQuotProvider]`,
    it makes the three `TAC.JetQuotShiftBridge3AtOrderQuot ...` instances
    available to typeclass search (via the existing installer module).
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderInstancesFromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-
  Re-export the three instances under the sole assumption
    [TAC.XiJetWindowEqAtOrderQuotProvider].

  (They are defined in the imported installer file, so these are just
   “named instance wrappers” that help you debug and `#check` them.)
-/

instance jetQuotShiftBridge3AtOrderQuot_w0At
    (m : ℕ) (s : OffSeed Xi) [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.JetQuotShiftBridge3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) := by
  infer_instance

instance jetQuotShiftBridge3AtOrderQuot_wp2At
    (m : ℕ) (s : OffSeed Xi) [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.JetQuotShiftBridge3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) := by
  infer_instance

instance jetQuotShiftBridge3AtOrderQuot_wp3At
    (m : ℕ) (s : OffSeed Xi) [TAC.XiJetWindowEqAtOrderQuotProvider] :
    TAC.JetQuotShiftBridge3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) := by
  infer_instance

end XiPacket
end Targets
end Hyperlocal
