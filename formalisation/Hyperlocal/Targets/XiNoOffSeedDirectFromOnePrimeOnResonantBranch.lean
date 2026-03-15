/-
  Hyperlocal/Targets/XiNoOffSeedDirectFromOnePrimeOnResonantBranch.lean

  Stronger last-mile contraction:

  because the nonresonant branch is already killed pointwise by the new
  no-pivot generic-prime W1 theorem, it is enough to prove just ONE prime
  sine-coefficient vanishing on the exact resonance branch.

  Concretely, either of the following branchwise hypotheses now suffices:

    ∀ off-seed s,  sin(t log(3/2)) = 0 -> bCoeff(...,2) = 0
  or
    ∀ off-seed s,  sin(t log(3/2)) = 0 -> bCoeff(...,3) = 0.

  On the exact resonance branch, vanishing at one of {2,3} propagates to the
  other by the explicit trigonometric relation
      log 3 = log 2 + log(3/2).
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_AllPrimesFromNonresonance_Pointwise
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy
import Hyperlocal.Targets.ZetaTransfer
import Hyperlocal.Cancellation.TwoPrimePhaseLock
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion
open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Exact resonance plus `sin(t log 2)=0` forces `sin(t log 3)=0`.
-/
lemma sin_log3_eq_zero_of_resonant_and_sin_log2_eq_zero
    {τ : ℝ}
    (hres : Real.sin (τ * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (h2 : Real.sin (τ * Real.log (2 : ℝ)) = 0) :
    Real.sin (τ * Real.log (3 : ℝ)) = 0 := by
  have hlog :
      Real.log (3 : ℝ) = Real.log (2 : ℝ) + Real.log ((3 : ℝ) / (2 : ℝ)) := by
    linarith [Hyperlocal.Targets.XiPacket.W1.log_three_div_two]
  have hmul :
      τ * Real.log (3 : ℝ)
        = τ * Real.log (2 : ℝ) + τ * Real.log ((3 : ℝ) / (2 : ℝ)) := by
    simpa [mul_add] using congrArg (fun x => τ * x) hlog
  rw [hmul, Real.sin_add]
  simp [h2, hres]

/--
Exact resonance plus `sin(t log 3)=0` forces `sin(t log 2)=0`.
-/
lemma sin_log2_eq_zero_of_resonant_and_sin_log3_eq_zero
    {τ : ℝ}
    (hres : Real.sin (τ * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (h3 : Real.sin (τ * Real.log (3 : ℝ)) = 0) :
    Real.sin (τ * Real.log (2 : ℝ)) = 0 := by
  have hlog :
      Real.log (2 : ℝ) = Real.log (3 : ℝ) - Real.log ((3 : ℝ) / (2 : ℝ)) := by
    linarith [Hyperlocal.Targets.XiPacket.W1.log_three_div_two]
  have hmul :
      τ * Real.log (2 : ℝ)
        = τ * Real.log (3 : ℝ) - τ * Real.log ((3 : ℝ) / (2 : ℝ)) := by
    simpa [sub_eq_add_neg, mul_add] using congrArg (fun x => τ * x) hlog
  rw [hmul, Real.sin_sub]
  simp [h3, hres]

/--
Exact resonance plus `bCoeff(...,2)=0` forces `bCoeff(...,3)=0`.
-/
lemma bCoeff3_eq_zero_of_resonant_and_bCoeff2_eq_zero
    (σ τ : ℝ)
    (hres : Real.sin (τ * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hb2 : bCoeff σ τ (2 : ℝ) = 0) :
    bCoeff σ τ (3 : ℝ) = 0 := by
  have hsin2 :
      Real.sin (τ * Real.log (2 : ℝ)) = 0 :=
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ) (t := τ) (p := (2 : ℝ)) (hb := hb2)
  have hsin3 :
      Real.sin (τ * Real.log (3 : ℝ)) = 0 :=
    sin_log3_eq_zero_of_resonant_and_sin_log2_eq_zero hres hsin2
  simp [bCoeff, hsin3]

/--
Exact resonance plus `bCoeff(...,3)=0` forces `bCoeff(...,2)=0`.
-/
lemma bCoeff2_eq_zero_of_resonant_and_bCoeff3_eq_zero
    (σ τ : ℝ)
    (hres : Real.sin (τ * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hb3 : bCoeff σ τ (3 : ℝ) = 0) :
    bCoeff σ τ (2 : ℝ) = 0 := by
  have hsin3 :
      Real.sin (τ * Real.log (3 : ℝ)) = 0 :=
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ) (t := τ) (p := (3 : ℝ)) (hb := hb3)
  have hsin2 :
      Real.sin (τ * Real.log (2 : ℝ)) = 0 :=
    sin_log2_eq_zero_of_resonant_and_sin_log3_eq_zero hres hsin3
  simp [bCoeff, hsin2]

/--
Pointwise contradiction from the exact resonance branch plus a prime-2
coefficient vanishing.
-/
theorem offSeed_false_of_resonant_and_bCoeff2_zero
    (s : Hyperlocal.OffSeed Xi)
    (hres : Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0) :
    False := by
  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
    bCoeff3_eq_zero_of_resonant_and_bCoeff2_eq_zero
      (σ := σ s) (τ := t s) (hres := hres) (hb2 := hb2)

  have hsin2 :
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 :=
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (2 : ℝ)) (hb := hb2)

  have hsin3 :
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 :=
    Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
      (σ := σ s) (t := t s) (p := (3 : ℝ)) (hb := hb3)

  have ht0 : t s = 0 :=
    Hyperlocal.Cancellation.PrimeWitness.two_prime_phase_lock
      (t s) ⟨hsin2, hsin3⟩

  have ht_ne : t s ≠ 0 := by
    simpa [XiPacket.t] using s.ht

  exact ht_ne ht0

/--
Pointwise contradiction from the exact resonance branch plus a prime-3
coefficient vanishing.
-/
theorem offSeed_false_of_resonant_and_bCoeff3_zero
    (s : Hyperlocal.OffSeed Xi)
    (hres : Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    False := by
  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
    bCoeff2_eq_zero_of_resonant_and_bCoeff3_eq_zero
      (σ := σ s) (τ := t s) (hres := hres) (hb3 := hb3)
  exact offSeed_false_of_resonant_and_bCoeff2_zero
    (s := s) (hres := hres) (hb2 := hb2)

/--
Global Xi-side endgame from the minimal resonant-branch obligation:

it is enough to prove `bCoeff(...,2)=0` on the exact resonance branch only.
-/
theorem noOffSeed_Xi_of_bCoeff2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (2 : ℝ) = 0) :
    NoOffSeed Xi := by
  intro hne
  rcases hne with ⟨s⟩
  by_cases hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
  · exact offSeed_false_of_resonant_and_bCoeff2_zero
      (s := s) (hres := hres) (hb2 := hb2_res s hres)
  · have htv :
        ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr hres
    have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
      XiPacket.bCoeff2_eq_zero_of_tval_ne_zero_pointwise (s := s) (htv := htv)
    have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
      XiPacket.bCoeff3_eq_zero_of_tval_ne_zero_pointwise (s := s) (htv := htv)

    have hsin2 :
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0 :=
      Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
        (σ := σ s) (t := t s) (p := (2 : ℝ)) (hb := hb2)

    have hsin3 :
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0 :=
      Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.sin_eq_zero_of_bCoeff_eq_zero
        (σ := σ s) (t := t s) (p := (3 : ℝ)) (hb := hb3)

    have ht0 : t s = 0 :=
      Hyperlocal.Cancellation.PrimeWitness.two_prime_phase_lock
        (t s) ⟨hsin2, hsin3⟩

    have ht_ne : t s ≠ 0 := by
      simpa [XiPacket.t] using s.ht

    exact ht_ne ht0

/--
Global Xi-side endgame from the symmetric minimal resonant-branch obligation
at prime `3`.
-/
theorem noOffSeed_Xi_of_bCoeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    NoOffSeed Xi := by
  have hb2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
    intro s hres
    exact bCoeff2_eq_zero_of_resonant_and_bCoeff3_eq_zero
      (σ := σ s) (τ := t s) (hres := hres) (hb3 := hb3_res s hres)
  exact noOffSeed_Xi_of_bCoeff2_zero_on_resonant_branch
    (hb2_res := hb2_res)

/--
ζ-side transfer from the minimal resonant-branch prime-2 obligation.
-/
theorem noOffSeed_Zeta_of_bCoeff2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (2 : ℝ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_bCoeff2_zero_on_resonant_branch (hb2_res := hb2_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
RH-facing export from the minimal resonant-branch prime-2 obligation.
-/
theorem criticalzero_zeta_of_bCoeff2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (2 : ℝ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_bCoeff2_zero_on_resonant_branch (hb2_res := hb2_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
ζ-side transfer from the symmetric minimal resonant-branch prime-3 obligation.
-/
theorem noOffSeed_Zeta_of_bCoeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_bCoeff3_zero_on_resonant_branch (hb3_res := hb3_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
RH-facing export from the symmetric minimal resonant-branch prime-3 obligation.
-/
theorem criticalzero_zeta_of_bCoeff3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hb3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (3 : ℝ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_bCoeff3_zero_on_resonant_branch (hb3_res := hb3_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
