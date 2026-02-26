/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProvider.lean

  Rec2-free provider of the *Toeplitz Row012 property* gate at order.

  This file exists so that true-analytic landing pads can depend on the Row012Prop gate
  WITHOUT importing any Rec2 interfaces / adapters.

  Downstream:
    [XiToeplitzRow012PropAtOrderTrueAnalytic]
      ⇒ (separate file) [XiJetQuotRec2AtOrderTrueAnalytic]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
True-analytic Toeplitz Row012 property gate (Rec2-free).

This is the exact “3 canonical windows” payload:
`ToeplitzRow012Prop s (w0At/wp2At/wp3At m s)`.
-/
class XiToeplitzRow012PropAtOrderTrueAnalytic : Prop where
  toeplitz_w0At  :
    ∀ (m : ℕ) (s : OffSeed Xi),
      ToeplitzRow012Prop s (w0At m s)
  toeplitz_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      ToeplitzRow012Prop s (wp2At m s)
  toeplitz_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      ToeplitzRow012Prop s (wp3At m s)

end XiPacket
end Targets
end Hyperlocal
