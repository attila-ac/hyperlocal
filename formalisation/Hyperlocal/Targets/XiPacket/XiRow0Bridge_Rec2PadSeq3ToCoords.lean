/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Rec2PadSeq3ToCoords.lean

  Pure algebra, cycle-safe:

  From a JetQuotRec2 recurrence on the padded sequence `padSeq3 w`,
  we extract explicit coordinate consequences for w : Window 3.

  Key point:
    JetQuotRec2 s (padSeq3 w) gives, at n=0,1,2, a linear system in w0,w1,w2,
    because padSeq3 w 3 = 0 etc.

  Under a minimal non-degeneracy hypothesis on coefficients, we can conclude
    w 2 = 0, w 1 = 0, w 0 = 0.

  This file deliberately does NOT assume where the recurrence comes from.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Convenience: name the three coefficients a0,a1,a2 used by JetQuotRec2.
-/
abbrev a0 (s : OffSeed Xi) : ℂ := JetQuotOp.aRk1 s 0
abbrev a1 (s : OffSeed Xi) : ℂ := JetQuotOp.aRk1 s 1
abbrev a2 (s : OffSeed Xi) : ℂ := JetQuotOp.aRk1 s 2

/--
From `JetQuotRec2 s (padSeq3 w)`, extract the n=2 equation:
  a0 * w2 = 0.
-/
theorem rec2_padSeq3_eq_n2
    (s : OffSeed Xi) (w : Window 3)
    (H : JetQuotRec2 s (padSeq3 w)) :
    (a0 s) * (w 2) = 0 := by
  -- n = 2:
  have h := H 2
  -- padSeq3 w 2 = w2, padSeq3 w 3 = 0, padSeq3 w 4 = 0
  simpa [JetQuotRec2, a0, a1, a2, padSeq3, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/--
From `JetQuotRec2 s (padSeq3 w)`, extract the n=1 equation:
  a0*w1 + a1*w2 = 0.
-/
theorem rec2_padSeq3_eq_n1
    (s : OffSeed Xi) (w : Window 3)
    (H : JetQuotRec2 s (padSeq3 w)) :
    (a0 s) * (w 1) + (a1 s) * (w 2) = 0 := by
  have h := H 1
  -- padSeq3 w 1 = w1, padSeq3 w 2 = w2, padSeq3 w 3 = 0
  simpa [JetQuotRec2, a0, a1, a2, padSeq3, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/--
From `JetQuotRec2 s (padSeq3 w)`, extract the n=0 equation:
  a0*w0 + a1*w1 + a2*w2 = 0.
-/
theorem rec2_padSeq3_eq_n0
    (s : OffSeed Xi) (w : Window 3)
    (H : JetQuotRec2 s (padSeq3 w)) :
    (a0 s) * (w 0) + (a1 s) * (w 1) + (a2 s) * (w 2) = 0 := by
  have h := H 0
  -- padSeq3 w 0 = w0, padSeq3 w 1 = w1, padSeq3 w 2 = w2
  simpa [JetQuotRec2, a0, a1, a2, padSeq3, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/--
Main algebraic consequence:

If `a0 s ≠ 0` then `JetQuotRec2 s (padSeq3 w)` forces `w2 = 0`, then `w1 = 0`,
and then `a0*w0 = 0` so `w0 = 0`.
-/
theorem coords_eq_zero_of_rec2_padSeq3
    (s : OffSeed Xi) (w : Window 3)
    (H : JetQuotRec2 s (padSeq3 w))
    (ha0 : a0 s ≠ 0) :
    w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 := by
  -- first: a0*w2 = 0
  have hw2' : (a0 s) * (w 2) = 0 := rec2_padSeq3_eq_n2 (s := s) (w := w) H
  have hw2 : w 2 = 0 := by
    exact (mul_eq_zero.mp hw2').resolve_left ha0

  -- then: a0*w1 + a1*w2 = 0 -> a0*w1 = 0
  have hw1' : (a0 s) * (w 1) = 0 := by
    have h1 : (a0 s) * (w 1) + (a1 s) * (w 2) = 0 := rec2_padSeq3_eq_n1 (s := s) (w := w) H
    simpa [hw2] using h1
  have hw1 : w 1 = 0 := by
    exact (mul_eq_zero.mp hw1').resolve_left ha0

  -- then: a0*w0 + a1*w1 + a2*w2 = 0 -> a0*w0 = 0
  have hw0' : (a0 s) * (w 0) = 0 := by
    have h0 : (a0 s) * (w 0) + (a1 s) * (w 1) + (a2 s) * (w 2) = 0 :=
      rec2_padSeq3_eq_n0 (s := s) (w := w) H
    simpa [hw1, hw2] using h0
  have hw0 : w 0 = 0 := by
    exact (mul_eq_zero.mp hw0').resolve_left ha0

  exact ⟨hw0, hw1, hw2⟩

end XiPacket
end Targets
end Hyperlocal
