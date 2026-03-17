import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2ConnectorDeterministic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface_GenericPrime
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
open Hyperlocal.Transport

/--
Remaining generic-prime burden, localized to the exact resonant branch only.

This is strictly smaller than the full class
`XiJetQuotRec2AtOrderTrueAnalyticPrime`: the nonresonant branch is already
discharged below by the deterministic W1 all-primes theorem.
-/
class XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider : Prop where
  rec2_wpAt_on_resonant32 :
    ∀ (m : ℕ) (s : OffSeed Xi) (p : ℕ),
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotRec2 s (padSeq3 (wpAt m s p))

/--
Nonresonant branch: the deterministic W1 all-primes theorem already gives
full Toeplitz annihilation of `wpAt m s p`, which converts to the padded
sequence recurrence by the existing row012 -> sequence bridge.
-/
theorem jetQuotRec2_wpAt_of_nonresonant32
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0) :
    JetQuotRec2 s (padSeq3 (wpAt m s p)) := by
  have htv :
      (((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) := by
    exact Complex.ofReal_ne_zero.mpr hres

  have hL :
      toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p) = 0 :=
    W1.toeplitzL_aRk1_wpAt_eq_zero_of_tval_ne_zero
      (m := m) (s := s) (p := p) htv

  have h0 :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0 := by
    simpa using congrFun hL (0 : Fin 3)

  have h1 :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (1 : Fin 3) = 0 := by
    simpa using congrFun hL (1 : Fin 3)

  have h2 :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (2 : Fin 3) = 0 := by
    simpa using congrFun hL (2 : Fin 3)

  exact
    jetQuotRec2_padSeq3_of_toeplitzRow012Prop
      (s := s)
      (w := wpAt m s p)
      ⟨h0, h1, h2⟩

/--
Full generic-prime recurrence payload from:

* the existing `{2,3}` true-analytic Rec2 root,
* the theorem-side quotient equality provider, and
* the *remaining* resonant-branch generic-prime producer only.

So after this file, the honest remaining root is no longer the whole global
generic-prime class, only its resonant-branch fragment.
-/
instance (priority := 1000)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider] :
    XiJetQuotRec2AtOrderTrueAnalyticPrime where
  rec2_wpAt := by
    intro m s p
    by_cases hres :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
    ·
      exact
        XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider.rec2_wpAt_on_resonant32
          (m := m) (s := s) (p := p) hres
    ·
      exact jetQuotRec2_wpAt_of_nonresonant32
        (m := m) (s := s) (p := p) hres

#print axioms jetQuotRec2_wpAt_of_nonresonant32

end XiPacket
end Targets
end Hyperlocal
