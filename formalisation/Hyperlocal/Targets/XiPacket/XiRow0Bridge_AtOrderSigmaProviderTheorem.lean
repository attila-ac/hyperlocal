/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTheorem.lean

  Historical compatibility surface for the AtOrder sigma bundle.

  CURRENT POLICY:
  * keep the historical constant name `xiAtOrderSigmaOut_axiom`
  * keep this file DAG-clean
  * do NOT import the Row0-frontier-at-order theorem route here

  Reason:
  this file sits on the consumer side of the row0 witness / concrete-extract
  corridor. If it imports the theorem route through
    `XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder`
  then it closes the cycle that blocks elimination of the Row0 frontier trio.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

axiom xiAtOrderSigmaOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s

instance (priority := 10) : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_axiom

end XiPacket
end Targets
end Hyperlocal
