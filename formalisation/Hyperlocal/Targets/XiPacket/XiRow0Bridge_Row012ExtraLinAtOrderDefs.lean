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

end XiPacket
end Targets
end Hyperlocal
