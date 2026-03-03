/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceInject.lean

  Boundary module (semantic cliff isolation).

  R2 cleanup: bCoeff(2)=0 and bCoeff(3)=0 are theorem-level, via the order-0
  Toeplitz identity path packaged in `XiToeplitzRecurrenceIdentity.lean`.

  This module keeps the legacy surface:
    it imports the order-0 nonvanishing injector so `[XiKappaAt0Nonzero s]`
    is available to downstream consumers, but the bCoeff facts are theorem-level.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0NonzeroInject

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Semantic injection: recurrence forces `bCoeff(2)=0` (theorem-level). -/
theorem xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) [XiKappaAt0Nonzero s] :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  -- Convert the order-0 seam `kappaAt0 s ≠ 0` into `kappaAt 0 s ≠ 0`.
  have hk0 : kappaAt (0 : ℕ) s ≠ 0 := by
    simpa [kappaAt0, kappaAt] using (XiKappaAt0Nonzero.kappa_ne0 (s := s))
  simpa using
    (xiToeplitzRecurrenceIdentity_p_of_kappaAt0 (s := s) hk0 (p := (2 : ℝ)) (Or.inl rfl))

/-- Semantic injection: recurrence forces `bCoeff(3)=0` (theorem-level). -/
theorem xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) [XiKappaAt0Nonzero s] :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  have hk0 : kappaAt (0 : ℕ) s ≠ 0 := by
    simpa [kappaAt0, kappaAt] using (XiKappaAt0Nonzero.kappa_ne0 (s := s))
  simpa using
    (xiToeplitzRecurrenceIdentity_p_of_kappaAt0 (s := s) hk0 (p := (3 : ℝ)) (Or.inr rfl))

end XiPacket
end Targets
end Hyperlocal
