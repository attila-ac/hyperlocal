/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3ExtractorAtOrder.lean

  Extract the Route–C `n=3` reverse convCoeff payloads for AtOrder windows
  from the already-available Route–B AtOrder row-0 Toeplitz annihilation.

  Cycle-safe: imports only Route–C algebra and the Route–B AtOrder frontier.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation
open Hyperlocal.Transport

/-- Extract the Route–C `n=3` reverse convCoeff payload for `w0At`. -/
theorem row0ConvCoeff3_w0At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_w0At (m := m) (s := s)
  have hs : row0Sigma s (w0At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

/-- Extract the Route–C `n=3` reverse convCoeff payload for `wp2At`. -/
theorem row0ConvCoeff3_wp2At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wp2At (m := m) (s := s)
  have hs : row0Sigma s (wp2At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

/-- Extract the Route–C `n=3` reverse convCoeff payload for `wp3At`. -/
theorem row0ConvCoeff3_wp3At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wp3At (m := m) (s := s)
  have hs : row0Sigma s (wp3At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs

end XiPacket
end Targets
end Hyperlocal
