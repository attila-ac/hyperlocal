/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromOutTrueAnalytic.lean

  Adapter:
    xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (bundle)
      ⇒ XiRow012ConvolutionAtRevAtOrderTrueAnalytic (3 window fields)

  This is intentionally SMALL and cycle-safe: it only projects fields.

  Note:
  `xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic` installs sigma locally from
  the Rec2 true-analytic gate (frontier-free), so this instance is Rec2-gated.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
If you have the sigma-free Row012 bundle theorem (true-analytic, Rec2-sourced),
you automatically get the fieldwise class used by the Tail345 manuscript builder.
-/
instance (priority := 900)
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_⟩
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s)).hw0At
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s)).hwp2At
  · intro m s
    exact (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
