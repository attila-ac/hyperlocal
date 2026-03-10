import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractFromWcStencil
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

structure XiJetQuotRow0ConcreteExtract (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

section
variable [TAC.XiJetWindowEqAtOrderQuotProvider]

def xiJetQuotRow0ConcreteExtract
    (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ConcreteExtract s := by
  let h := xiJetQuotRow0ConcreteExtract_fromWcStencil (s := s)
  exact ⟨h.hop_w0, h.hop_wc, h.hop_wp2, h.hop_wp3⟩

end

end XiPacket
end Targets
end Hyperlocal
