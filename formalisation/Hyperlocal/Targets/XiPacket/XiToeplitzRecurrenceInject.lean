import Mathlib.Tactic
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- ξ Toeplitz/recurrence injection at p=2 (now theorematic). -/
theorem xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  simpa using
    (Hyperlocal.Targets.XiPacket.xiToeplitzRecurrenceIdentity_p
      (s := s) (p := (2 : ℝ)) (hp := Or.inl rfl))

/-- ξ Toeplitz/recurrence injection at p=3 (now theorematic). -/
theorem xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  simpa using
    (Hyperlocal.Targets.XiPacket.xiToeplitzRecurrenceIdentity_p
      (s := s) (p := (3 : ℝ)) (hp := Or.inr rfl))

end Hyperlocal.Targets.XiPacket
