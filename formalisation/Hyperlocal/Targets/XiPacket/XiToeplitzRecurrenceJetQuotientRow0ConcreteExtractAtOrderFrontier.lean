/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier.lean

  Frontier discharge module (cycle-safe).

  CHANGE (2026-02-22, Path-A refactor follow-up):
  The frontier witness is now delegated to the cycle-safe Gate-from-analytic alias,
  instead of importing the Heart module.

  Motivation:
  * The Heart module may depend on the analytic extractor stack.
  * The GateFromAnalytic module is explicitly designed to avoid importing Heart/Frontier/extractor,
    and to depend only on GateDefs + the Route–B endpoint.

  IMPORTANT (Lean 4.23):
  `XiJetQuotRow0ConcreteExtractAtOrder m s : Type`, so this frontier is a `def`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Frontier witness (Type-level): delegated to the cycle-safe gate-from-analytic alias.

This avoids importing the Heart/extractor stack into the frontier module.
Once the Route–B endpoint is theorem-level, this definition becomes axiom-free
without downstream edits.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_frontier
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
