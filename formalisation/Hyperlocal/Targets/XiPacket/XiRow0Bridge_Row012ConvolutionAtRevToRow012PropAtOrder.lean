/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevToRow012PropAtOrder.lean

  Discharge: Row012 reverse-stencil payload bundle (AtOrder) ⇒ Prop-level Toeplitz rows 0/1/2
  payload bundle (AtOrder).

  Cycle-safe: uses only defs + already-established bridge
  `toeplitzRow012Prop_of_row012ConvolutionAtRev`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
If you have an AtOrder bundle providing `Row012ConvolutionAtRev` for `w0At/wp2At/wp3At`,
then you get the Prop-level manuscript endpoint `XiJetQuotRow012PropAtOrder`.
-/
theorem xiJetQuotRow012PropAtOrder_of_row012ConvolutionAtRevAtOrder
    (m : ℕ) (s : OffSeed Xi)
    (H : XiRow012ConvolutionAtRevAtOrderOut m s) :
    XiJetQuotRow012PropAtOrder m s := by
  refine XiJetQuotRow012PropAtOrder.ofProp (m := m) (s := s) ?_ ?_ ?_
  · exact toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) (H := H.hw0At)
  · exact toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) (H := H.hwp2At)
  · exact toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) (H := H.hwp3At)

end XiPacket
end Targets
end Hyperlocal
