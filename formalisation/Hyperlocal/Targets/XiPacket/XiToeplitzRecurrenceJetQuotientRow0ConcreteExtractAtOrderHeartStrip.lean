/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartStrip.lean

  Strip-specialised wrapper for the Row0 heart output.

  This file is intentionally thin: it just re-exports the analytic-strip heart
  theorem at the strip surface, while exposing the Route-A quotient-window gate
  required by the underlying proof.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartFromAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
Preferred strip wrapper name.
-/
theorem xiJetQuotRow0AtOrderHeartOut_fromAnalyticStrip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0AtOrderHeartOut m (s : OffSeed Xi) := by
  exact
    xiJetQuotRow0AtOrderHeartOut_strip (m := m) (s := s)

/--
Compatibility alias: some downstream files still use the underscored spelling.
-/
theorem xiJetQuotRow0AtOrderHeartOut_fromAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0AtOrderHeartOut m (s : OffSeed Xi) := by
  exact
    xiJetQuotRow0AtOrderHeartOut_fromAnalyticStrip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
