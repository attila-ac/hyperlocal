/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot.lean

  Cycle-safe “JetQuot → Jet (quotient arm)” bridge statement layer.

  Parallel to `TACTransportTruncated_JetQuotShiftBridgeAtOrder.lean`,
  but targets the Route-A quotient model jet semantics:

      IsJet3AtOrderQuot m s z w := IsJet3At (routeA_G s) z w

  This file contains NO axioms.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

/--
ONE semantic connector (quotient arm):

`JetQuotShiftBridge3AtOrderQuot m s z w` means that whenever the JetQuot recurrence holds on
`padSeq3 w`, the window `w` is a genuine 3-jet of the Route-A quotient function
`routeA_G s` at anchor `z`.
-/
class JetQuotShiftBridge3AtOrderQuot
    (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) : Prop where
  jet_of_rec2 :
    JetQuotRec2 s (padSeq3 w) → IsJet3AtOrderQuot m s z w

/-- If the recurrence holds and we have the bridge, we can view `w0At m s` as a quotient jet at `z`. -/
theorem isJet3AtOrderQuot_w0At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrderQuot m s z (w0At m s)]
    (H : JetQuotRec2 s (padSeq3 (w0At m s))) :
    IsJet3AtOrderQuot m s z (w0At m s) :=
  JetQuotShiftBridge3AtOrderQuot.jet_of_rec2
    (m := m) (s := s) (z := z) (w := w0At m s) H

/-- Same pattern for `wp2At`. -/
theorem isJet3AtOrderQuot_wp2At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrderQuot m s z (wp2At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp2At m s))) :
    IsJet3AtOrderQuot m s z (wp2At m s) :=
  JetQuotShiftBridge3AtOrderQuot.jet_of_rec2
    (m := m) (s := s) (z := z) (w := wp2At m s) H

/-- Same pattern for `wp3At`. -/
theorem isJet3AtOrderQuot_wp3At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrderQuot m s z (wp3At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp3At m s))) :
    IsJet3AtOrderQuot m s z (wp3At m s) :=
  JetQuotShiftBridge3AtOrderQuot.jet_of_rec2
    (m := m) (s := s) (z := z) (w := wp3At m s) H

/-
  Handy “zero-jet at anchor” lemma (quotient arm):

  If you also know w0=w1=w2=0, then the jet statement collapses to concrete equalities
  for the function `routeA_G s` at `z`.
-/

/-- From `IsJet3AtOrderQuot m s z w` and coordinates 0, get the three analytic equalities for `routeA_G s` at `z`. -/
theorem jet_values_eq_zero_of_coords_zero_atOrderQuot
    (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (Hjet : IsJet3AtOrderQuot m s z w)
    (Hw0 : w 0 = 0) (Hw1 : w 1 = 0) (Hw2 : w 2 = 0) :
    (routeA_G s) z = 0 ∧ deriv (routeA_G s) z = 0 ∧ deriv (deriv (routeA_G s)) z = 0 := by
  -- unfold the quotient-jet predicate to an `IsJet3At` statement
  have Hjet' : IsJet3At (routeA_G s) z w := by
    simpa [IsJet3AtOrderQuot] using Hjet
  rcases Hjet' with ⟨h0, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [Hw0] using h0.symm
  · simpa [Hw1] using h1.symm
  · simpa [Hw2] using h2.symm

end TAC

end XiPacket
end Targets
end Hyperlocal
