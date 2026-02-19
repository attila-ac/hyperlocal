/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB.lean

  Route–B analytic recurrence endpoint (AtOrder, row-0 concrete extract).

  Lean 4.23 note:
    Since `XiJetQuotRow0ConcreteExtractAtOrder m s` is Type-valued,
    this exported endpoint must be a `def`, not a `theorem`.

  Big sweep (2026-02-19):
    The endpoint is now axiom-free. The only remaining semantic cliff lives in

      `xiJetQuotOpZeroAtOrder : ∀ m s, XiJetQuotOpZeroAtOrder m s`

    from `XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean`.
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

/-- Route–B endpoint (AtOrder): package the raw Toeplitz row-0 witness into the Type-level extract bundle. -/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s := by
  have hC : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder (m := m) (s := s)
  exact ⟨hC.hop_w0At, hC.hop_wp2At, hC.hop_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
