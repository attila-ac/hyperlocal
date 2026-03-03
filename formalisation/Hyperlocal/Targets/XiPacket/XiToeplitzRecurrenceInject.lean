/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceInject.lean

  Injection boundary for the Toeplitz recurrence consumer.

  Target end-state (pivot-gate):
  * NO dependency on the legacy anchor injector chain.
  * Consume only the pivot gate `[XiKappaPivotNonzero s]`.

  This file is theorem-only: it provides the `bCoeff(2)=0` / `bCoeff(3)=0` consequences
  in a convenient API for downstream, but does not install any new instances.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaPivotNonzero

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Consumer lemma: `bCoeff(2)=0` from the Toeplitz recurrence, via the pivot gate. -/
theorem xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) [XiKappaPivotNonzero s] :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  -- Use the already packaged `{2,3}` wrapper.
  simpa using
    (xiToeplitzRecurrenceIdentity_p (s := s) (p := (2 : ℝ)) (Or.inl rfl))

/-- Consumer lemma: `bCoeff(3)=0` from the Toeplitz recurrence, via the pivot gate. -/
theorem xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) [XiKappaPivotNonzero s] :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  simpa using
    (xiToeplitzRecurrenceIdentity_p (s := s) (p := (3 : ℝ)) (Or.inr rfl))

end XiPacket
end Targets
end Hyperlocal
