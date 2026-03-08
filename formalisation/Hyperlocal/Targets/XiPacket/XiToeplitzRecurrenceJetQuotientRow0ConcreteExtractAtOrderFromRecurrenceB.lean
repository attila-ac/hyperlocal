/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB.lean

  Route–B analytic recurrence endpoint (AtOrder, row-0 concrete extract).

  Lean 4.23 note:
    Since `XiJetQuotRow0ConcreteExtractAtOrder m s` is Type-valued,
    this exported endpoint must be a `def`, not a `theorem`.

  Consumer retarget:
    this file now consumes the theorem-level row-0 witness
      `xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream`
    directly, rather than the historical public wrapper
      `xiJetQuotRow0WitnessCAtOrder`.

  IMPORTANT:
  * this is a theorem-only downstream retarget
  * it avoids importing the public Row0 semantics wrapper here
  * it does not by itself remove any remaining axiom from the end cone
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route–B endpoint (AtOrder):
package the theorem-level row-0 witness into the Type-level concrete extract bundle.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0ConcreteExtractAtOrder m s := by
  have hC : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  exact ⟨hC.hop_w0At, hC.hop_wp2At, hC.hop_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
