/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderAxiom.lean

  DAG-clean placeholder instance: provides the AtOrder sigma bundle by axiom.

  Import this in analytic-only upstream provider modules to keep the project building
  while the true analytic proof is installed.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Placeholder (DAG-clean) sigma provider. Replace by a theorem-level instance later. -/
axiom xiAtOrderSigmaOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s

instance : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_axiom

end XiPacket
end Targets
end Hyperlocal
