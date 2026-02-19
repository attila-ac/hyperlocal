/-
  Hyperlocal/Targets/XiPacket/XiRow0Coeff3CoreAtOrderProof.lean

  Discharge the AtOrder coeff-3 boundary directly from the cycle-safe Gate
  (Row0ConvolutionAtRev → row0Sigma = 0), avoiding the outer frontier chain.

  NOTE:
  `XiRow0Coeff3CoreAtOrder.lean` already declares `row0ConvCoeff3_*` as axioms,
  so we export theorem-level proofs under `_proof` names only.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Cancellation

theorem row0ConvCoeff3_w0At_proof (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
  have hs : row0Sigma s (w0At m s) = 0 := by
    rcases (xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s)) with ⟨h0, -, -⟩
    exact h0
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

theorem row0ConvCoeff3_wp2At_proof (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
  have hs : row0Sigma s (wp2At m s) = 0 := by
    rcases (xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s)) with ⟨-, h2, -⟩
    exact h2
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

theorem row0ConvCoeff3_wp3At_proof (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
  have hs : row0Sigma s (wp3At m s) = 0 := by
    rcases (xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s)) with ⟨-, -, h3⟩
    exact h3
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs

end XiPacket
end Targets
end Hyperlocal
