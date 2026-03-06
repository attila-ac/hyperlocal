/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB.lean

  Route–B analytic recurrence endpoint (AtOrder, row-0 concrete extract).

  Lean 4.23 note:
    Since `XiJetQuotRow0ConcreteExtractAtOrder m s` is Type-valued,
    this exported endpoint must be a `def`, not a `theorem`.

  GRAPH-SURGERY UPDATE:
    This file no longer imports the historical public semantics surface

      `XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean`

    just to obtain the row-0 witness bundle.
    Instead it consumes the new theorem-level upstream file

      `XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream.lean`

    which breaks the back-edge responsible for the sigma-import cycle.

  This is a graph cleanup step; it does not by itself claim end-cone reduction.
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

/-- Route–B endpoint (AtOrder): package the raw Toeplitz row-0 witness into the Type-level extract bundle. -/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s := by
  have hC : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream (m := m) (s := s)
  exact ⟨hC.hop_w0At, hC.hop_wp2At, hC.hop_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
