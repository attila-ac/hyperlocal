/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB.lean

  Route–B analytic recurrence endpoint (AtOrder, row-0 concrete extract).

  Lean 4.23 note:
    Since `XiJetQuotRow0ConcreteExtractAtOrder m s` is Type-valued,
    this exported endpoint must be a `def`, not a `theorem`.

  Consumer retarget:
    this file now consumes the theorem-level row-0 witness
      `xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream`
    directly.

  2026-03-13 honest post-axiom state:
  * the old global coords01 fallback provider has been removed
  * therefore this endpoint can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

/--
Route–B endpoint (AtOrder):
package the theorem-level row-0 witness into the Type-level concrete extract bundle.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow0ConcreteExtractAtOrder m s := by
  have hC : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  exact ⟨hC.hop_w0At, hC.hop_wp2At, hC.hop_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
