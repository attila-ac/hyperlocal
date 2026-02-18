/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence.lean

  Cycle-safe placeholder for the *concrete order-`m` jet-quotient recurrence extraction theorem*.

  Purpose:
  The AtOrder “analytic heart” file should not carry an axiom directly.
  Instead, it should *derive* its Prop-level contract from the (future) concrete
  analytic recurrence extraction theorem.

  Status:
  * The intended concrete theorem is not yet formalised.
  * For now, we isolate its exact Type-level output as a single axiom.

  When the true analytic extraction layer is implemented, replace the axiom in
  this file by a theorem and leave all downstream files unchanged.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Concrete (Type-level) order-`m` jet-quotient recurrence extraction output.

This is the *analytic extraction theorem* in its strongest form: it provides the three
row-0 Toeplitz annihilations for `w0At/wp2At/wp3At` with coefficients
`JetQuotOp.aRk1 s`.

Replace this axiom by a theorem once the analytic extraction layer is formalised.
-/
axiom xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s

end XiPacket
end Targets
end Hyperlocal
