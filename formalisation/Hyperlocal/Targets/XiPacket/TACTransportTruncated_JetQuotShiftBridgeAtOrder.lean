/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetQuotShiftBridgeAtOrder.lean

  Cycle-safe “JetQuot → Jet (at order m)” bridge statement layer.

  This is the order-m analogue of `TACTransportTruncated_JetQuotShiftBridge.lean`.

  Instead of `IsJet3At Xi z w`, we target the correct semantics for the
  jet-pivot windows:

      IsJet3AtOrder m z w  := IsJet3At (cderivIter m Xi) z w

  This matches `XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderDefs
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
ONE semantic connector (order-m):

`JetQuotShiftBridge3AtOrder m s z w` means that whenever the JetQuot recurrence holds on
`padSeq3 w`, the window `w` is a genuine 3-jet of the *m-th derivative function*
`cderivIter m Xi` at anchor `z`.
-/
class JetQuotShiftBridge3AtOrder (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3) : Prop where
  jet_of_rec2 :
    JetQuotRec2 s (padSeq3 w) → IsJet3AtOrder m z w

/-- If the recurrence holds and we have the bridge, we can view `w0At m s` as an order-m jet at `z`. -/
theorem isJet3AtOrder_w0At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrder m s z (w0At m s)]
    (H : JetQuotRec2 s (padSeq3 (w0At m s))) :
    IsJet3AtOrder m z (w0At m s) :=
  JetQuotShiftBridge3AtOrder.jet_of_rec2 (m := m) (s := s) (z := z) (w := w0At m s) H

/-- Same pattern for `wp2At`. -/
theorem isJet3AtOrder_wp2At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrder m s z (wp2At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp2At m s))) :
    IsJet3AtOrder m z (wp2At m s) :=
  JetQuotShiftBridge3AtOrder.jet_of_rec2 (m := m) (s := s) (z := z) (w := wp2At m s) H

/-- Same pattern for `wp3At`. -/
theorem isJet3AtOrder_wp3At_of_rec2
    (m : ℕ) (s : OffSeed Xi) (z : ℂ)
    [JetQuotShiftBridge3AtOrder m s z (wp3At m s)]
    (H : JetQuotRec2 s (padSeq3 (wp3At m s))) :
    IsJet3AtOrder m z (wp3At m s) :=
  JetQuotShiftBridge3AtOrder.jet_of_rec2 (m := m) (s := s) (z := z) (w := wp3At m s) H

/-
  A handy “zero-jet at anchor” lemma (order-m):

  If you also know w0=w1=w2=0, then the jet statement collapses to concrete equalities
  for the function `cderivIter m Xi` at `z`.
-/

/-- From `IsJet3AtOrder m z w` and coordinates 0, get the three analytic equalities for `cderivIter m Xi` at `z`. -/
theorem jet_values_eq_zero_of_coords_zero_atOrder
    (m : ℕ) (z : ℂ) (w : Window 3)
    (Hjet : IsJet3AtOrder m z w)
    (Hw0 : w 0 = 0) (Hw1 : w 1 = 0) (Hw2 : w 2 = 0) :
    (cderivIter m Xi) z = 0 ∧ deriv (cderivIter m Xi) z = 0 ∧ deriv (deriv (cderivIter m Xi)) z = 0 := by
  rcases Hjet with ⟨h0, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [Hw0] using h0.symm
  · simpa [Hw1] using h1.symm
  · simpa [Hw2] using h2.symm

end TAC

end XiPacket
end Targets
end Hyperlocal
