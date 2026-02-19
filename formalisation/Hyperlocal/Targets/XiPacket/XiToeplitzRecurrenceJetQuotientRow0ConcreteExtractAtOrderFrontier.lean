/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier.lean

  Frontier discharge module (cycle-safe).

  CHANGE (2026-02-18):
  Build the Type-level Toeplitz witness from the *scalar* heart contract
  using `...AtOrderScalarize.lean`.

  IMPORTANT (Lean 4.23):
  `XiJetQuotRow0ConcreteExtractAtOrder m s : Type`, so this frontier is a `def`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize

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

Once the recurrence extraction endpoint is theorem-level, this `def` becomes axiom-free
without downstream edits.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_frontier
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s := by
  classical
  -- bind the heart output once (robust against elaboration/projection brittleness)
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  -- package scalar equalities into the Type-level Toeplitz witness
  exact
    xiJetQuotRow0ConcreteExtractAtOrder_of_row0Sigma (m := m) (s := s)
      (hw0At := H.hw0AtSigma)
      (hwp2At := H.hwp2AtSigma)
      (hwp3At := H.hwp3AtSigma)

end XiPacket
end Targets
end Hyperlocal
