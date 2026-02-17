import Hyperlocal.Targets.XiTransportOp
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

noncomputable section
namespace Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport
open scoped BigOperators
open Complex

-- If Window n has an Add/SMul instance (it usually does), these will go through.

theorem XiTransportOp2_add (s : OffSeed Xi) (w₁ w₂ : Window 3) :
    (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (w₁ + w₂)
      = (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w₁
      + (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w₂ := by
  ext i
  simp [Hyperlocal.Targets.XiTransport.XiTransportOp]

theorem XiTransportOp2_smul (s : OffSeed Xi) (a : ℂ) (w : Window 3) :
    (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (a • w)
      = a • (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w := by
  ext i
  simp [Hyperlocal.Targets.XiTransport.XiTransportOp]

end Hyperlocal.Targets.XiPacket
