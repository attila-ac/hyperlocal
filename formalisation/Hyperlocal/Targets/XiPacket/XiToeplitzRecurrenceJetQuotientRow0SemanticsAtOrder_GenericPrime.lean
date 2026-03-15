import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface_GenericPrime
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-
  Generic-prime recurrence -> actual Toeplitz row/full zero for `wpAt m s p`.

  This is the missing upstream producer behind the explicit `hwpop` hole
  isolated in the generic-prime ell/identity lane.
-/

private lemma toeplitzL_eq_zero_of_rows
    {s : OffSeed Xi} {w : Hyperlocal.Transport.Window 3}
    (h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0)
    (h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0)
    (h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) = 0 := by
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

private lemma row0_eq_zero_of_rec2_wpAt
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0 := by
  have hrec : JetQuotRec2 s (padSeq3 (wpAt m s p)) :=
    XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := p)
  have h0' :
      (JetQuotOp.aRk1 s 0) * (wpAt m s p) 0
        + (JetQuotOp.aRk1 s 1) * (wpAt m s p) 1
        + (JetQuotOp.aRk1 s 2) * (wpAt m s p) 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 0)
  simpa [toeplitzL_two_apply_fin0, add_assoc, add_left_comm, add_comm] using h0'

private lemma row1_eq_zero_of_rec2_wpAt
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (1 : Fin 3) = 0 := by
  have hrec : JetQuotRec2 s (padSeq3 (wpAt m s p)) :=
    XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := p)
  have h1' :
      (JetQuotOp.aRk1 s 0) * (wpAt m s p) 1
        + (JetQuotOp.aRk1 s 1) * (wpAt m s p) 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 1)
  simpa [toeplitzL_two_apply_fin1, add_assoc, add_left_comm, add_comm] using h1'

private lemma row2_eq_zero_of_rec2_wpAt
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (2 : Fin 3) = 0 := by
  have hrec : JetQuotRec2 s (padSeq3 (wpAt m s p)) :=
    XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := p)
  have h2' :
      (JetQuotOp.aRk1 s 0) * (wpAt m s p) 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 2)
  simpa [toeplitzL_two_apply_fin2] using h2'

/--
The missing generic-prime row-0 producer.

This is the exact `hwpop` theorem surface that the generic-prime ell/identity
lane was waiting for.
-/
theorem xiJetQuot_row0_wpAt_of_trueAnalyticPrime
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0 := by
  exact row0_eq_zero_of_rec2_wpAt (m := m) (s := s) (p := p)

/--
Stronger full-window version: the actual Toeplitz operator annihilates the
entire prime window `wpAt m s p`.
-/
theorem xiJetQuot_wpAt_eq_zero_of_trueAnalyticPrime
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p) = 0 := by
  exact toeplitzL_eq_zero_of_rows
    (s := s) (w := wpAt m s p)
    (row0_eq_zero_of_rec2_wpAt (m := m) (s := s) (p := p))
    (row1_eq_zero_of_rec2_wpAt (m := m) (s := s) (p := p))
    (row2_eq_zero_of_rec2_wpAt (m := m) (s := s) (p := p))

end XiPacket
end Targets
end Hyperlocal
