/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFrontier.lean

  Frontier discharge module (cycle-safe).

  FIX:
  Your current environment still has the \emph{Toeplitz-field} heart contract
  (fields `hw0At/hwp2At/hwp3At`), not the scalar-field version.
  So we:
    1) read the Toeplitz row-0 equalities from the heart,
    2) rewrite each into `row0Sigma = 0` using `toeplitzL_row0_eq_row0Sigma`,
    3) package via `xiJetQuotRow0ConcreteExtractAtOrder_of_row0Sigma`.

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

Once `xiJetQuotRow0AtOrderHeartOut` is proved as a theorem, this `def` becomes
axiom-free without downstream edits.
-/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_frontier
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  -- Convert the heart's Toeplitz row-0 equalities into scalar `row0Sigma = 0`.
  have hw0AtSigma : row0Sigma s (w0At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)] using H.hw0At

  have hwp2AtSigma : row0Sigma s (wp2At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)] using H.hwp2At

  have hwp3AtSigma : row0Sigma s (wp3At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)] using H.hwp3At

  -- Package scalar equalities into the Type-level Toeplitz witness.
  exact
    xiJetQuotRow0ConcreteExtractAtOrder_of_row0Sigma (m := m) (s := s)
      hw0AtSigma hwp2AtSigma hwp3AtSigma

end XiPacket
end Targets
end Hyperlocal
