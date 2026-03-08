import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

/-- Route--B “AtOrder” ℓ-output (theorem-level; proof is upstream). -/
theorem xiToeplitzEllOutAt_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOutAt m s :=
  xiToeplitzEllOutAt_fromRecurrenceC_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
