/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTheorem.lean

  Historical compatibility surface for the AtOrder sigma bundle.

  2026-03-13 sigma kill:
  * keep the historical constant name `xiAtOrderSigmaOut_axiom`
  * redefine it theoremically from the Row0-frontier-at-order bridge
  * keep the installed `XiAtOrderSigmaProvider` instance on this stable import path

  Import-cycle check:
  `XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder` depends only on
  the provider interface, the Row0-frontier `_spec` facts, and the Toeplitz→sigma
  algebra bridge; it does not depend back on this file.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Transport

/--
Historical compatibility name, now theorem-backed from the Row0-frontier route.
-/
theorem xiAtOrderSigmaOut_axiom
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderSigmaOut m s :=
  xiAtOrderSigmaOut_fromRow0FrontierAtOrder (m := m) (s := s)

instance (priority := 10)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderSigmaProvider where
  sigma := by
    intro m s
    exact xiAtOrderSigmaOut_axiom (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
