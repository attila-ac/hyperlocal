/-
PATCH (REPLACE FILE CONTENT) for:
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Extractor.lean

Fix:
  Your build cycle is caused by importing Row0Concrete / Row0ConcreteProof, which
  (via Row0Analytic) depends back on Route–C files.

This version imports ONLY the cycle-safe Route–B frontier file.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Frontier
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

/-- Extract the Route–C `n=3` reverse convCoeff payload for `w0`. -/
theorem row0ConvCoeff3_w0 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_w0 s
  have hs : row0Sigma s (w0 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0 s)] using hs

/-- Extract the Route–C `n=3` reverse convCoeff payload for `wc`. -/
theorem row0ConvCoeff3_wc (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wc s
  have hs : row0Sigma s (wc s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] using hs

/-- Extract the Route–C `n=3` reverse convCoeff payload for `wp2`. -/
theorem row0ConvCoeff3_wp2 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wp2 s
  have hs : row0Sigma s (wp2 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2 s)] using hs

/-- Extract the Route–C `n=3` reverse convCoeff payload for `wp3`. -/
theorem row0ConvCoeff3_wp3 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 := by
  have ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 :=
    xiJetQuot_row0_wp3 s
  have hs : row0Sigma s (wp3 s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3 s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3 s)] using hs

end XiPacket
end Targets
end Hyperlocal
