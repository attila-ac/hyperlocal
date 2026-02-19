/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3ExtractorAtOrder.lean

  Cycle-safe extractor for the Route--C `n=3` reverse Cauchy coefficient payload
  at *order m* (jet-pivot windows).

  Purpose:
  Provide the finite coefficient identity

    convCoeff (row0CoeffSeqRev s) (winSeqRev (w?At m s)) 3 = 0

  derived purely from the already-packaged Route--B AtOrder frontier:

    xiJetQuot_row0_w0At / xiJetQuot_row0_wp2At / xiJetQuot_row0_wp3At

  This mirrors `XiRow0Bridge_Row0Coeff3Extractor.lean` (order-0), but for the
  AtOrder jet-pivot windows.

  No new axioms; imports remain cycle-safe.
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

/-- Extract the Route--C `n=3` reverse convCoeff payload for `w0At m`. -/
theorem row0ConvCoeff3_w0At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_w0At (m := m) (s := s)
  have hs : row0Sigma s (w0At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

/-- Extract the Route--C `n=3` reverse convCoeff payload for `wp2At m`. -/
theorem row0ConvCoeff3_wp2At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wp2At (m := m) (s := s)
  have hs : row0Sigma s (wp2At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

/-- Extract the Route--C `n=3` reverse convCoeff payload for `wp3At m`. -/
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
