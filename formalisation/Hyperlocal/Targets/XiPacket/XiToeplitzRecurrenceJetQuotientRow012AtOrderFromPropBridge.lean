/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromPropBridge.lean

  Bridge: from the Prop-valued manuscript endpoint `XiJetQuotRow012PropAtOrder m s`
  to the Type-valued Route–A landing target `XiJetQuotRow012AtOrder m s`.

  This is cycle-safe and defs-only with respect to the extractor stack:
  it consumes only the Prop payload, and packages its proof fields into the
  Type-valued structure.

  Motivation:
  * The extractor-facing endpoint is Type-valued (`XiJetQuotRow012AtOrder`).
  * In many analytic contexts, it is more natural to prove the Prop payload first.
  * This file ensures you can later implement the upstream analytic endpoint by
    proving only `XiJetQuotRow012PropAtOrder` and then lifting via this bridge.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Package the Prop-valued row012 payload into the Type-valued target bundle. -/
noncomputable def xiJetQuotRow012AtOrder_of_row012PropAtOrder
    (m : ℕ) (s : OffSeed Xi) (H : XiJetQuotRow012PropAtOrder m s) :
    XiJetQuotRow012AtOrder m s := by
  classical
  -- unpack the conjunctive Prop payload
  rcases H with ⟨Hw0, Hrest⟩
  rcases Hrest with ⟨Hwp2, Hwp3⟩

  -- row-0 witness for the Type bundle
  have h0 : XiJetQuotRow0WitnessCAtOrder m s :=
    ⟨Hw0.h0, Hwp2.h0, Hwp3.h0⟩

  -- remaining row-1/2 equalities are already present
  exact
    ⟨h0,
      Hw0.h1, Hw0.h2,
      Hwp2.h1, Hwp2.h2,
      Hwp3.h1, Hwp3.h2⟩

end XiPacket
end Targets
end Hyperlocal
