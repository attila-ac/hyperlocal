import Hyperlocal.Targets.OffSeedPhaseLockXiPayload

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXi

open scoped Real
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

theorem offSeedPhaseLock_Xi :
  Hyperlocal.Transport.OffSeedPhaseLock (H := Xi) := by
  have h :
      Hyperlocal.Transport.OffSeedPhaseLock (H := Hyperlocal.xi) :=
    Hyperlocal.Targets.OffSeedPhaseLockXiPayload.offSeedPhaseLock_Xi
  simpa [Xi] using h

end OffSeedPhaseLockXi
end Targets
end Hyperlocal
