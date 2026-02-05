import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiTransportOp          -- NEW (so the axiom is visibly “from XiTransportOp”)
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.DetFromWindow
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXiPayload

open scoped Real

abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- THE only semantic cliff: from XiTransportOp's window/Toeplitz recurrence build a `WindowPayload`. -/
axiom xiWindowPayload_of_window :
    ∀ s : Hyperlocal.OffSeed Xi,
      Hyperlocal.Targets.XiPacket.WindowPayload (s.ρ.re) (s.ρ.im)   -- CHANGED

/-- Convenience: extracted trig packet payload (definitional). -/
noncomputable def xiPrimeTrigPacket (s : Hyperlocal.OffSeed Xi) :
    Hyperlocal.Transport.PrimeTrigPacket.Packet (s.ρ.re) (s.ρ.im) :=
  (xiWindowPayload_of_window s).toPrimeTrigPacket                  -- CHANGED

/-- ξ satisfies the OffSeedPhaseLock contract. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  simpa using
    Hyperlocal.Transport.PrimeTrigPacket.offSeedPhaseLock_of_packet (xiPrimeTrigPacket s)

end OffSeedPhaseLockXiPayload
end Targets
end Hyperlocal
