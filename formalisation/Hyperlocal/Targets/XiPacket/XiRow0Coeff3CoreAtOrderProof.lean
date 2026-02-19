/-
  Hyperlocal/Targets/XiPacket/XiRow0Coeff3CoreAtOrderProof.lean

  Discharge the AtOrder coeff-3 boundary from the AtOrder frontier
  (Toeplitz row-0 annihilation), producing theorem-level facts.

  This file is allowed to import the frontier/concrete proof layers.
  The upstream Core file will re-export these theorems and become axiom-free.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiTransportConvolution

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Cancellation

theorem row0ConvCoeff3_w0At_proof
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (w0At m s)) 3 = 0 := by
  have ht := xiJetQuot_row0_w0At (m := m) (s := s)
  have hs : row0Sigma s (w0At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

theorem row0ConvCoeff3_wp2At_proof
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp2At m s)) 3 = 0 := by
  have ht := xiJetQuot_row0_wp2At (m := m) (s := s)
  have hs : row0Sigma s (wp2At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

theorem row0ConvCoeff3_wp3At_proof
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp3At m s)) 3 = 0 := by
  have ht := xiJetQuot_row0_wp3At (m := m) (s := s)
  have hs : row0Sigma s (wp3At m s) = 0 := by
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)] using ht
  simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs

end XiPacket
end Targets
end Hyperlocal
