/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayload.lean

  Canonical Stage-3 consumer (Lean 69 path).

  This file intentionally avoids:
    • WindowPayload / WindowPayloadFacts
    • any Packet constructor / m = 0 fallback path
    • any direct dependency on XiWindowScNonvanishing

  It re-exports the dslope-native Or-κ consumer proven in
  `OffSeedPhaseLockXiPayloadAtOrder.lean`.
-/

import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-- Canonical target function. Matches the rest of the Targets layer. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Canonical Stage-3 theorem (re-export). -/
abbrev offSeedPhaseLock_Xi
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider] :
    Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

end Targets
end Hyperlocal
