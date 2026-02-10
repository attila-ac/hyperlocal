import Mathlib.Tactic
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs

-- Option B pieces already exist here:
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceBridge

-- Option A pieces already exist here (bCoeff-level facts via recurrence identity):
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceSemantics

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-
Option A (direct bCoeff-level phase lock)
-/

/-- “Phase lock” phrased directly at the bCoeff level. -/
def XiRecurrencePhaseLock (s : Hyperlocal.OffSeed Xi) : Prop :=
  bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
  bCoeff (σ s) (t s) (3 : ℝ) = 0

/-- Local wrapper: matches the name you tried to use. -/
theorem xiBcoeff2_eq_zero (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
  xiToeplitz_hb2_fromRecurrence (s := s)

/-- Local wrapper: matches the name you tried to use. -/
theorem xiBcoeff3_eq_zero (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
  xiToeplitz_hb3_fromRecurrence (s := s)

/--
Hook A: recurrence extraction gives phase lock.
(Currently discharged by the existing recurrence→bCoeff lemmas; later replace by manuscript proof.)
-/
theorem xiRecurrencePhaseLock_fromMinimalModel (s : Hyperlocal.OffSeed Xi) :
    XiRecurrencePhaseLock s := by
  exact ⟨xiBcoeff2_eq_zero s, xiBcoeff3_eq_zero s⟩


/-
Option B (Toeplitz/window span-out)
-/
/-
NOTE:
`XiToeplitzSpanOut`, `xiToeplitzSpanOut_fromRecurrence`,
and `xiToeplitzEllOut_fromRecurrence` are ALREADY declared in the imported
`XiToeplitzRecurrenceOut/Bridge`. Do not redeclare them here.
-/

/-- Convenience alias with a *new* name (optional). -/
abbrev XiToeplitzSpanOutB := XiToeplitzSpanOut

/-- Convenience alias with a *new* name (optional). -/
abbrev xiToeplitzSpanOut_fromRecurrenceB := xiToeplitzSpanOut_fromRecurrence

/-- Convenience: recurrence ⇒ ell-out (theorem already exists; this is just a new name). -/
theorem xiToeplitzEllOut_fromRecurrenceB (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s := by
  exact xiToeplitzEllOut_fromRecurrence (s := s)

end Hyperlocal.Targets.XiPacket
