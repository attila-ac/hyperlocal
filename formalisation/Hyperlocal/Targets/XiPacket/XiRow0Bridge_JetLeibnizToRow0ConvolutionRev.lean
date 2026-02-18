/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizToRow0ConvolutionRev.lean

  MOVE–3: bridge Jet–Leibniz payload to the Route–C Row--0 reverse convolution gate.

  Current status:
  * The repo now has theorem-level Route–B extraction for the *canonical* windows.
  * A fully general derivation
        JetLeibnizAt s z w → convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0
    is NOT derivable from the three Leibniz equalities alone (h0/h1/h2),
    so the bridge remains the (single) semantic insertion point.

  This file therefore reinstates that bridge as an axiom, but keeps the surface API
  stable and cycle-safe.

  Once you later expose an actual theorem that proves `row0ConvCoeff3_eq_zero_of_JetLeibnizAt`,
  you can delete the axiom and keep everything downstream unchanged.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

/--
**Semantic insertion point (single remaining axiom at Move–3).**

A theorem-level proof of this statement cannot be obtained from `h0/h1/h2` alone,
so it is isolated here as the unique remaining ξ-specific bridge.
-/
axiom row0ConvCoeff3_eq_zero_of_JetLeibnizAt
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetLeibnizAt s z w →
      convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0

/-- The single Route–C Row--0 bridge: Leibniz ⇒ reverse Row--0 convolution gate. -/
theorem row0ConvolutionAtRev_of_JetLeibnizAt
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetLeibnizAt s z w → Row0ConvolutionAtRev s z w := by
  intro hL
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  have h3 :
      convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 := by
    exact row0ConvCoeff3_eq_zero_of_JetLeibnizAt
      (s := s) (z := z) (w := w) (by exact ⟨G, hfac, hjet, h0, h1, h2⟩)
  exact ⟨G, hfac, hjet, h3⟩

namespace JetLeibnizToRow0ConvolutionRevExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvCoeff3_eq_zero_of_JetLeibnizAt
   row0ConvolutionAtRev_of_JetLeibnizAt)
end JetLeibnizToRow0ConvolutionRevExport

end XiPacket
end Targets
end Hyperlocal
