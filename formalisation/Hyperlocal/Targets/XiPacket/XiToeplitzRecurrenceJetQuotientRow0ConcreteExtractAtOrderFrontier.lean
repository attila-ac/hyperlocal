/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier.lean

  Frontier discharge module (cycle-safe):

  IMPORTANT (Lean 4.23):
  `XiJetQuotRow0ConcreteExtractAtOrder m s : Type`, so this frontier must be a `def`,
  not a `theorem`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Frontier witness (Type-level): build the extraction witness from the analytic heart output.

Once `xiJetQuotRow0AtOrderHeartOut` is proved as a theorem, this `def` becomes
axiom-free without downstream edits.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_frontier
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact (xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)).hw0At
  · exact (xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)).hwp2At
  · exact (xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
