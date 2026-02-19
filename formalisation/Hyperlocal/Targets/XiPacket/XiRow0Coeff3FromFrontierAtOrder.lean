import Hyperlocal.Targets.XiPacket.XiRow0Coeff3CoreAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof

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


-- repeat for wp2At / wp3At

end XiPacket
end Targets
end Hyperlocal
