/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_NonresonantContradiction.lean

  After the strengthened W1 nonresonant route now reaches arbitrary-prime
  `bCoeff(σ(s), t(s), p) = 0`, the next clean consequence is to collapse the
  entire nonresonant branch.

  Logic:
    sin(t log(3/2)) ≠ 0
      -> (by the new generic-prime W1 file) bCoeff(...,2)=0 and bCoeff(...,3)=0
      -> sin(t log 2)=0 and sin(t log 3)=0
      -> t = 0   (two-prime phase lock)
      -> contradiction with `s.ht`.

  This does NOT yet prove the remaining scalar identity globally.
  What it does prove is that, under the current theorem-side W1 route,
  every surviving off-seed is forced onto the exact resonance branch.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_AllPrimesFromNonresonance
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Cancellation.TwoPrimePhaseLock
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/--
If the current W1 nonresonant branch were active at an off-seed `s`,
the all-primes W1 consequence would force `bCoeff(...,2)=0` and `bCoeff(...,3)=0`,
hence `sin(t log 2)=0` and `sin(t log 3)=0`, hence `t=0`, contradicting `s.ht`.
So the nonresonant branch is impossible.
-/
theorem nonresonant_branch_impossible
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    False := by
  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
    bCoeff_eq_zero_of_tval_ne_zero (s := s) (p := 2) (htv := htv)

  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
    bCoeff_eq_zero_of_tval_ne_zero (s := s) (p := 3) (htv := htv)

  have hsin2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
    exact Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (2 : ℝ)) (hb := hb2)

  have hsin3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
    exact Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (3 : ℝ)) (hb := hb3)

  have ht0 : t s = 0 :=
    Hyperlocal.Cancellation.PrimeWitness.two_prime_phase_lock (t s) ⟨hsin2, hsin3⟩

  have ht_ne : t s ≠ 0 := by
    simpa [XiPacket.t] using s.ht

  exact ht_ne ht0

/--
Real-valued localisation theorem:
under the current theorem-side W1 route, every off-seed is forced onto the exact
resonance branch `sin(t log(3/2)) = 0`.
-/
theorem sin_log_three_div_two_eq_zero_of_pivot_gate
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s] :
    Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_contra hsin
  have htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hsin
  exact nonresonant_branch_impossible (s := s) (htv := htv)

/--
Complex-valued version of the same exact-resonance conclusion.
-/
theorem tval23_eq_zero_of_pivot_gate
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s] :
    ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) = 0 := by
  exact Complex.ofReal_eq_zero.mpr
    (sin_log_three_div_two_eq_zero_of_pivot_gate (s := s))

end XiPacket
end Targets
end Hyperlocal
