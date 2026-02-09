/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceSemantics.lean

  Phase 2: kernel + conversion, with a single open lemma.
  IMPORTANT: this file must NOT define `xiToeplitzEllOut_fromRecurrence`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/--
Kernel-level output (semantic target).

For now: exactly SpanOut, but packaged as an `extends` record so you can later
add Toeplitz/recurrence kernel facts without touching downstream plumbing.
-/
structure XiToeplitzKernelOut (s : Hyperlocal.OffSeed Xi) : Prop
    extends toSpanOut : XiToeplitzSpanOut s

/-- Pure algebra: KernelOut gives EllOut (via SpanOut ⇒ EllOut). -/
theorem XiToeplitzEllOut_of_kernel (s : Hyperlocal.OffSeed Xi)
    (k : XiToeplitzKernelOut s) : XiToeplitzEllOut s :=
  XiToeplitzEllOut.of_spanOut (s := s) (k.toSpanOut)

/--
THE single remaining ξ-semantic theorem (open, temporary).
This is the only `sorry` in the Toeplitz/recurrence layer.
-/
theorem xiToeplitzKernelOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzKernelOut s := by
  sorry

end XiPacket
end Targets
end Hyperlocal
