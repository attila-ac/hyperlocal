/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB.lean

  Route–B analytic recurrence endpoint (AtOrder, row-0 concrete extract).

  Lean 4.23 note:
    Since `XiJetQuotRow0ConcreteExtractAtOrder m s` is Type-valued,
    this exported endpoint must be a `def`, not a `theorem`.

  Consumer retarget:
    this file now consumes the public Row0 semantic witness
      `xiJetQuotRow0WitnessCAtOrder`
    rather than any historical row0 spec surface.

  IMPORTANT:
  * this is a consumer-layer cleanup
  * it does not by itself resolve the remaining dirty adapter/import path
  * the currently measured obstruction sits upstream in
      `xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic`
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route–B endpoint (AtOrder):
package the row-0 semantic witness into the Type-level concrete extract bundle.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0ConcreteExtractAtOrder m s := by
  have hC : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder (m := m) (s := s)
  exact ⟨hC.hop_w0At, hC.hop_wp2At, hC.hop_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
