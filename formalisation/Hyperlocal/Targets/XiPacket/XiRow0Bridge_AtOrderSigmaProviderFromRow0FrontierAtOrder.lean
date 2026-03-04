import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderAxiom
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpec
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_ToeplitzRow0ToRow0Sigma

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

theorem xiAtOrderSigmaOut_fromRow0FrontierAtOrder
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := w0At m s)
      (xiJetQuot_row0_w0At (m := m) (s := s))
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := wp2At m s)
      (xiJetQuot_row0_wp2At (m := m) (s := s))
  ·
    exact row0Sigma_eq_zero_of_toeplitz_row0_eq_zero (s := s) (w := wp3At m s)
      (xiJetQuot_row0_wp3At (m := m) (s := s))

instance (priority := 1000) : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromRow0FrontierAtOrder

end XiPacket
end Targets
end Hyperlocal
