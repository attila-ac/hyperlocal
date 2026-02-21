/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromHeart.lean

  Pure projection: extract the Row012ExtraLin constraints for the three AtOrder windows
  from the strengthened Route–B heart output.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Prop bundle: extra linear constraints for the three AtOrder windows. -/
structure XiRow012ExtraLinAtOrderOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row012ExtraLin s (w0At m s)
  hwp2At : Row012ExtraLin s (wp2At m s)
  hwp3At : Row012ExtraLin s (wp3At m s)

/-- Projection: strengthened heart output implies the extra-lin bundle. -/
theorem xiRow012ExtraLinAtOrderOut_fromHeart
    (m : ℕ) (s : OffSeed Xi) :
    XiRow012ExtraLinAtOrderOut m s := by
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)
  exact ⟨H.hw0AtExtra, H.hwp2AtExtra, H.hwp3AtExtra⟩

end XiPacket
end Targets
end Hyperlocal
