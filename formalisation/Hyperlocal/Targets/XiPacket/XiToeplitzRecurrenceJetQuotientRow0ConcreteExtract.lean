/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract.lean

  Concrete recurrence-extraction frontier (Route B, jet-quotient).

  Semantic input Route B needs:
    `toeplitzL 2 (JetQuotOp.aRk1 s)` annihilates row 0 of `w0/wc/wp2/wp3`.

  This file is axiom-free: the only remaining ξ-specific proofs live in
  `XiToeplitzRecurrenceJetQuotientRow0Concrete.lean` (the four canonical lemmas).

  NOTE:
  `toeplitzL` and `Window` live in `Hyperlocal.Transport`, so we `open` that namespace
  (otherwise you will see “unknown identifier toeplitzL / Window”).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Concrete
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Row-0 recurrence extraction bundle for the jet-quotient Toeplitz operator on the
four canonical ξ windows `w0/wc/wp2/wp3`.
-/
structure XiJetQuotRow0ConcreteExtract (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

/-!
### Canonical-window interface
-/

/-- The four canonical ξ windows used by Route B. -/
inductive XiJetQuotCanonicalWindow (s : Hyperlocal.OffSeed Xi) : Window 3 → Prop
  | w0  : XiJetQuotCanonicalWindow s (w0 s)
  | wc  : XiJetQuotCanonicalWindow s (wc s)
  | wp2 : XiJetQuotCanonicalWindow s (wp2 s)
  | wp3 : XiJetQuotCanonicalWindow s (wp3 s)

/--
Concrete ξ row-0 recurrence extraction for canonical windows.

Thin case-split wrapper around the four concrete lemmas proved in
`XiToeplitzRecurrenceJetQuotientRow0Concrete.lean`.
-/
theorem xiJetQuot_row0_of_canonical (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
  XiJetQuotCanonicalWindow s w →
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  intro hw
  cases hw with
  | w0  => simpa using xiJetQuot_row0_w0  (s := s)
  | wc  => simpa using xiJetQuot_row0_wc  (s := s)
  | wp2 => simpa using xiJetQuot_row0_wp2 (s := s)
  | wp3 => simpa using xiJetQuot_row0_wp3 (s := s)

/-- Package the canonical-window row-0 identities into the bundled extract. -/
def xiJetQuotRow0ConcreteExtract (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ConcreteExtract s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.w0  (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wc  (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wp2 (s := s))
  · exact xiJetQuot_row0_of_canonical (s := s) (XiJetQuotCanonicalWindow.wp3 (s := s))

/-!
### Operator-level branding (row-0 only)

`JetQuotOp.jetQuotToeplitzOp3 s` is a `toeplitzL 2 (JetQuotOp.aRk1 s)` operator.
Full-window annihilation is intentionally *not* the target; Route B consumes only
the row-0 scalar coordinate.
-/

/-- Official Route-B semantic target (row-0 only), phrased via the operator. -/
theorem xiJetQuot_op3_fin0_of_canonical (s : Hyperlocal.OffSeed Xi) {w : Window 3} :
  XiJetQuotCanonicalWindow s w →
    (JetQuotOp.jetQuotToeplitzOp3 s w) (0 : Fin 3) = 0 := by
  intro hw
  -- unfold the operator as `toeplitzL` and reuse the canonical row-0 theorem
  simpa [JetQuotOp.jetQuotToeplitzOp3] using (xiJetQuot_row0_of_canonical (s := s) (w := w) hw)

end XiPacket
end Targets
end Hyperlocal
