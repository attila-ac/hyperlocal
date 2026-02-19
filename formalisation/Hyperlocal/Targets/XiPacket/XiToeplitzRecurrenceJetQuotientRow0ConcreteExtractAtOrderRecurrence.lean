/-
  TEMPORARY SHIM (cycle-safe): route the old “Recurrence” endpoint through Gate.
-/
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiJetQuotRow0AtOrderConvolutionOut_axiom_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderConvolutionOut m s :=
  xiJetQuotRow0AtOrderConvolutionOut_axiom (m := m) (s := s)

noncomputable def xiJetQuotRow0ScalarGoalsAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ScalarGoalsAtOrder m s :=
  xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s)

noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_fromGate (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
