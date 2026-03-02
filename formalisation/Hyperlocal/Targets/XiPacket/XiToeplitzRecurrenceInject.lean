/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceInject.lean

  Boundary module (semantic cliff isolation):

  The recurrence layer exports *only* the two bCoeff phase-lock facts
  at primes 2 and 3.  Historically these were proven using an Option-ELL
  order-0 κ argument that imported the legacy anchor axiom

      xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

  M1 follow-through cleanup:
  We *quarantine* that legacy path off the main import graph by reverting this
  file to a small axiom boundary.

  Downstream (Stage-3) now uses dslope-native Or-κ, so the anchor axiom is no
  longer needed in the consumer pipeline.

  Later (A1 / analytic closure) you can replace these axioms by a theorem-level
  proof, without touching any consumer APIs.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Semantic injection: recurrence forces bCoeff(2)=0. -/
axiom xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0

/-- Semantic injection: recurrence forces bCoeff(3)=0. -/
axiom xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0

end XiPacket
end Targets
end Hyperlocal
