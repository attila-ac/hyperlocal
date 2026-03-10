import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Hyperlocal.Transport

structure XiJetQuotRow0RecurrenceExtract (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

section
variable [TAC.XiJetWindowEqAtOrderQuotProvider]

def xiJetQuotRow0RecurrenceExtract (s : Hyperlocal.OffSeed Xi) :
  XiJetQuotRow0RecurrenceExtract s := by
  let h : XiJetQuotRow0ConcreteExtract s := xiJetQuotRow0ConcreteExtract (s := s)
  exact ⟨h.hop_w0, h.hop_wc, h.hop_wp2, h.hop_wp3⟩

def xiJetQuotRow0WitnessC (s : Hyperlocal.OffSeed Xi) : XiJetQuotRow0WitnessC s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (xiJetQuotRow0RecurrenceExtract (s := s)).hop_w0
  · exact (xiJetQuotRow0RecurrenceExtract (s := s)).hop_wc
  · exact (xiJetQuotRow0RecurrenceExtract (s := s)).hop_wp2
  · exact (xiJetQuotRow0RecurrenceExtract (s := s)).hop_wp3

end

end XiPacket
end Targets
end Hyperlocal
