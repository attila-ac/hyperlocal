/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrderFacade.lean

  Theorem-level sigma provider derived from the Route–B row-0 frontier-at-order.

  PURPOSE:
    This is an axiom-free replacement for `XiRow0Bridge_AtOrderSigmaProviderAxiom`,
    but it lives in a separate module to avoid import cycles with the analytic extractor chain.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Re-exported theorem-level σ-output at order. -/
theorem xiAtOrderSigmaOut_fromRow0FrontierAtOrder_facade
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s := by
  simpa using (xiAtOrderSigmaOut_fromRow0FrontierAtOrder (m := m) (s := s))

/-- Theorem-level σ provider instance (facade). -/
instance (priority := 1900) : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromRow0FrontierAtOrder_facade

end XiPacket
end Targets
end Hyperlocal
