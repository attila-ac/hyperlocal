/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridge.lean

  Cycle-safe “JetQuot → Jet” bridge statement layer.

  We already have:
    * JetQuotRec2 s (padSeq3 w)  : purely algebraic recurrence in the JetQuot model
    * coords_eq_zero_of_rec2_padSeq3 : extracts w0=w1=w2=0 under a0≠0

  What we do NOT yet have theorem-level (this is the real analytic connector):
    * that the JetQuot window `w` corresponds to the *actual derivative jet*
      of Xi at the intended anchor point.

  This file isolates that missing connector behind ONE knob:
    `JetQuotShiftBridge3`.

  Later discharge site (non-cycle-safe):
    prove instances of `JetQuotShiftBridge3` from the analytic extractor / quotient model.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_WindowJetBridge
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_WindowJetBridge_wp2wp3
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

/--
ONE semantic connector:

`JetQuotShiftBridge3 m s z w` means that whenever the JetQuot recurrence holds on
`padSeq3 w`, the window `w` is a genuine 3-jet of `Xi` at anchor `z`.

This is exactly the “analytic content” that must eventually be proved from your
quotient/Taylor model, but we keep it abstract and cycle-safe.
-/
class JetQuotShiftBridge3 (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) : Prop where
  jet_of_rec2 :
    JetQuotRec2 s (padSeq3 w) → IsJet3At Xi z w

/-
  Immediate corollary pattern you will use downstream:

  From extractor: JetQuotRec2 on padSeq3 (w0At/wp2At/wp3At)
  + bridge: IsJet3At at the correct anchor
  + coords extraction: w0=w1=w2=0
  ⇒ actual derivative values at the anchor are 0 (hence Xi z = 0 etc).
-/

/-- If the recurrence holds and we have the bridge, we can view `w0At m s` as a 3-jet at `z`. -/
theorem isJet3At_w0At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3 m s z (w0At m s)]
    (H : JetQuotRec2 s (padSeq3 (w0At m s))) :
    IsJet3At Xi z (w0At m s) :=
  JetQuotShiftBridge3.jet_of_rec2 (m := m) (s := s) (z := z) (w := w0At m s) H

/-- Same pattern for `wp2At`. -/
theorem isJet3At_wp2At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3 m s z (wp2At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp2At m s))) :
    IsJet3At Xi z (wp2At m s) :=
  JetQuotShiftBridge3.jet_of_rec2 (m := m) (s := s) (z := z) (w := wp2At m s) H

/-- Same pattern for `wp3At`. -/
theorem isJet3At_wp3At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3 m s z (wp3At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp3At m s))) :
    IsJet3At Xi z (wp3At m s) :=
  JetQuotShiftBridge3.jet_of_rec2 (m := m) (s := s) (z := z) (w := wp3At m s) H

/-
  A handy “zero-jet at anchor” lemma:

  If you also know w0=w1=w2=0, then the jet statement collapses to concrete equalities
  Xi z = 0, deriv Xi z = 0, deriv (deriv Xi) z = 0.
-/

/-- From `IsJet3At Xi z w` and coordinates 0, get the three analytic equalities at `z`. -/
theorem jet_values_eq_zero_of_coords_zero
    (z : ℂ) (w : Window 3)
    (Hjet : IsJet3At Xi z w)
    (Hw0 : w 0 = 0) (Hw1 : w 1 = 0) (Hw2 : w 2 = 0) :
    Xi z = 0 ∧ deriv Xi z = 0 ∧ deriv (deriv Xi) z = 0 := by
  rcases Hjet with ⟨h0, h1, h2⟩
  -- h0 : w 0 = Xi z, etc
  refine ⟨?_, ?_, ?_⟩
  · simpa [Hw0] using h0.symm
  · simpa [Hw1] using h1.symm
  · simpa [Hw2] using h2.symm

end TAC

end XiPacket
end Targets
end Hyperlocal
