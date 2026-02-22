/-(
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRow012ConvolutionAtRevAtOrder.lean

  Path-A algebraic bridge:

    Row012 reverse-stencil payload at order m
      (XiRow012ConvolutionAtRevAtOrderOut m s)
    ==> Prop-level Toeplitz row012 payload at order m
      (XiJetQuotRow012PropAtOrder m s).

  This is cycle-safe:
  * consumes only the row012 reverse-stencil Prop bundle,
  * uses the purely algebraic projection
      toeplitzRow012Prop_of_row012ConvolutionAtRev
    to obtain Toeplitz row equalities.

  No extractor / heart imports.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Path-A bridge (AtOrder):
row012 reverse-stencil payload implies Prop-level Toeplitz row012 payload.
-/
theorem xiJetQuotRow012PropAtOrder_of_row012ConvolutionAtRevAtOrderOut
    (m : ℕ) (s : OffSeed Xi)
    (H : XiRow012ConvolutionAtRevAtOrderOut m s) :
    XiJetQuotRow012PropAtOrder m s := by
  classical

  have hw0 : ToeplitzRow012Prop s (w0At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) H.hw0At

  have hwp2 : ToeplitzRow012Prop s (wp2At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H.hwp2At

  have hwp3 : ToeplitzRow012Prop s (wp3At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) H.hwp3At

  exact XiJetQuotRow012PropAtOrder.ofProp (m := m) (s := s) hw0 hwp2 hwp3

end XiPacket
end Targets
end Hyperlocal
