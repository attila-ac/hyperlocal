import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpec
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_ToeplitzRow0ToRow0Sigma

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

theorem xiAtOrderSigmaOut_fromRow0FrontierAtOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderSigmaOut m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := w0At m s)
      (xiJetQuot_row0_w0At_spec (m := m) (s := s))
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := wp2At m s)
      (xiJetQuot_row0_wp2At_spec (m := m) (s := s))
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := wp3At m s)
      (xiJetQuot_row0_wp3At_spec (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
