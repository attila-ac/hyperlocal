/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractFromWcStencil.lean

  Parallel gated extract consuming the theorem-side row-0 concrete producer
  from `...Row0ConcreteFromWcStencil`.

  This file is intentionally parallel to the historical ungated
  `XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

structure XiJetQuotRow0ConcreteExtractFromWcStencil (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

inductive XiJetQuotCanonicalWindowFromWcStencil
    (s : Hyperlocal.OffSeed Xi) : Window 3 → Prop
  | w0  : XiJetQuotCanonicalWindowFromWcStencil s (w0 s)
  | wc  : XiJetQuotCanonicalWindowFromWcStencil s (wc s)
  | wp2 : XiJetQuotCanonicalWindowFromWcStencil s (wp2 s)
  | wp3 : XiJetQuotCanonicalWindowFromWcStencil s (wp3 s)

section

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

theorem xiJetQuot_row0_of_canonical_fromWcStencil
    (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
    XiJetQuotCanonicalWindowFromWcStencil s w →
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  intro hw
  cases hw with
  | w0  => simpa using xiJetQuot_row0_w0_fromWcStencil  (s := s)
  | wc  => simpa using xiJetQuot_row0_wc_fromWcStencil  (s := s)
  | wp2 => simpa using xiJetQuot_row0_wp2_fromWcStencil (s := s)
  | wp3 => simpa using xiJetQuot_row0_wp3_fromWcStencil (s := s)

def xiJetQuotRow0ConcreteExtract_fromWcStencil
    (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ConcreteExtractFromWcStencil s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xiJetQuot_row0_of_canonical_fromWcStencil (s := s)
      (XiJetQuotCanonicalWindowFromWcStencil.w0 (s := s))
  · exact xiJetQuot_row0_of_canonical_fromWcStencil (s := s)
      (XiJetQuotCanonicalWindowFromWcStencil.wc (s := s))
  · exact xiJetQuot_row0_of_canonical_fromWcStencil (s := s)
      (XiJetQuotCanonicalWindowFromWcStencil.wp2 (s := s))
  · exact xiJetQuot_row0_of_canonical_fromWcStencil (s := s)
      (XiJetQuotCanonicalWindowFromWcStencil.wp3 (s := s))

theorem xiJetQuot_op3_fin0_of_canonical_fromWcStencil
    (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
    XiJetQuotCanonicalWindowFromWcStencil s w →
      (JetQuotOp.jetQuotToeplitzOp3 s w) (0 : Fin 3) = 0 := by
  intro hw
  simpa [JetQuotOp.jetQuotToeplitzOp3] using
    (xiJetQuot_row0_of_canonical_fromWcStencil (s := s) (w := w) hw)

end

end XiPacket
end Targets
end Hyperlocal
