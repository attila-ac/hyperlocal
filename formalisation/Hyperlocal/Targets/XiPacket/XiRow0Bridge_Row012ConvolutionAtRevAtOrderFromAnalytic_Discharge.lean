/-
  Once `Row012ExtraLin` is proven for the three AtOrder windows, this file
  discharges the remaining admitted boundary with no further refactors.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- The remaining analytic obligation: the two extra linear constraints for each AtOrder window. -/
structure XiRow012ExtraLinAtOrderOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row012ExtraLin s (w0At m s)
  hwp2At : Row012ExtraLin s (wp2At m s)
  hwp3At : Row012ExtraLin s (wp3At m s)

/--
If you can prove `XiRow012ExtraLinAtOrderOut m s` from your analytic chain,
then you get the full `Row012ConvolutionAtRev` payload and can delete the axiom.
-/
theorem xiRow012ConvolutionAtRevAtOrderOut_of_extraLin
    (m : ℕ) (s : OffSeed Xi)
    (HL : XiRow012ExtraLinAtOrderOut m s) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row012ConvolutionAtRev_w0At_fromAnalytic_of_extraLin (m := m) (s := s) HL.hw0At
  · exact row012ConvolutionAtRev_wp2At_fromAnalytic_of_extraLin (m := m) (s := s) HL.hwp2At
  · exact row012ConvolutionAtRev_wp3At_fromAnalytic_of_extraLin (m := m) (s := s) HL.hwp3At

end XiPacket
end Targets
end Hyperlocal
