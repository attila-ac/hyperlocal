import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider
import Hyperlocal.Targets.XiPacket.XiRouteA_WcScalarNormalizationProvider

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Rec2PadSeq3ToCoords
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticRecurrencesStrict
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
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
open Complex
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket
open Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder

/--
The final resonant branch closes by contradiction from the already-available
true-analytic `wp2At/wp3At` Rec2 payload.

Idea:
* strict Rec2 on `w0At/wp2At/wp3At` gives coordinate-0/1/2 vanishing;
* the definitional decompositions
    `wp2At = w0At + a₂ • wc + b₂ • ws`
    `wp3At = w0At + a₃ • wc + b₃ • ws`
  together with the closed forms
    `wc = e1 + δ • e2`, `ws = e2`
  force `a₂ = b₂ = a₃ = b₃ = 0`;
* hence `sin(t log 2) = 0` and `sin(t log 3) = 0`;
* the existing two-prime phase lock yields `t = 0`, contradicting `OffSeed`.
-/
theorem rec2_wpAt_on_resonant32_closed
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    ∀ (m : ℕ) (s : OffSeed Xi) (p : ℕ),
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotRec2 s (padSeq3 (wpAt m s p)) := by
  intro m s p hres
  classical

  -- First get the local nondegeneracy needed by `coords_eq_zero_of_rec2_padSeq3`.
  rcases offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs_strip : (ss : OffSeed Xi) = s := by
    rfl

  have ha0 : JetQuotOp.aRk1 s 0 ≠ 0 := by
    simpa [hs_strip] using (a0_ne_zero_of_strip (s := ss))

  -- Strict true-analytic Rec2 already exists on `w0At`, `wp2At`, `wp3At`.
  have hw0 :
      (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3
      (s := s) (w := w0At m s)
      (H := xiJetQuotRec2_padSeq3_w0At_fromAnalytic_strict (m := m) (s := s))
      (ha0 := ha0)

  have hwp2 :
      (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3
      (s := s) (w := wp2At m s)
      (H := xiJetQuotRec2_padSeq3_wp2At_fromAnalytic_strict (m := m) (s := s))
      (ha0 := ha0)

  have hwp3 :
      (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords_eq_zero_of_rec2_padSeq3
      (s := s) (w := wp3At m s)
      (H := xiJetQuotRec2_padSeq3_wp3At_fromAnalytic_strict (m := m) (s := s))
      (ha0 := ha0)

  -- Extract the coefficient vanishing forced by the concrete `wc/ws` shapes.
  have ha2_zero : aCoeff (σ s) (t s) (2 : ℝ) = 0 := by
    have hcoord1 : (wp2At m s) 1 = 0 := hwp2.2.1
    have hw0_1 : (w0At m s) 1 = 0 := hw0.2.1
    rw [wp2At, wpAt] at hcoord1
    simp [hw0_1, wc_eq_basis, ws_eq_basis, basisW3, e1, e2] at hcoord1
    simpa [XiPacket.σ, XiPacket.t] using hcoord1

  have ha3_zero : aCoeff (σ s) (t s) (3 : ℝ) = 0 := by
    have hcoord1 : (wp3At m s) 1 = 0 := hwp3.2.1
    have hw0_1 : (w0At m s) 1 = 0 := hw0.2.1
    rw [wp3At, wpAt] at hcoord1
    simp [hw0_1, wc_eq_basis, ws_eq_basis, basisW3, e1, e2] at hcoord1
    simpa [XiPacket.σ, XiPacket.t] using hcoord1

  have hb2_zero : bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
    have hcoord2 : (wp2At m s) 2 = 0 := hwp2.2.2
    have hw0_2 : (w0At m s) 2 = 0 := hw0.2.2
    rw [wp2At, wpAt] at hcoord2
    simp [hw0_2, ha2_zero, wc_eq_basis, ws_eq_basis, basisW3, e1, e2] at hcoord2
    simpa [XiPacket.σ, XiPacket.t] using hcoord2

  have hb3_zero : bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
    have hcoord2 : (wp3At m s) 2 = 0 := hwp3.2.2
    have hw0_2 : (w0At m s) 2 = 0 := hw0.2.2
    rw [wp3At, wpAt] at hcoord2
    simp [hw0_2, ha3_zero, wc_eq_basis, ws_eq_basis, basisW3, e1, e2] at hcoord2
    simpa [XiPacket.σ, XiPacket.t] using hcoord2

  -- Convert `bCoeff = 0` to sine vanishing.
  have hsin2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
    simpa [XiPacket.σ, XiPacket.t] using
      (sin_eq_zero_of_bCoeff_eq_zero
        (σ := σ s) (t := t s) (p := (2 : ℝ)) hb2_zero)

  have hsin3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
    simpa [XiPacket.σ, XiPacket.t] using
      (sin_eq_zero_of_bCoeff_eq_zero
        (σ := σ s) (t := t s) (p := (3 : ℝ)) hb3_zero)

  have ht_zero : t s = 0 :=
    Hyperlocal.Cancellation.PrimeWitness.two_prime_phase_lock (t s) ⟨hsin2, hsin3⟩

  have ht_ne : t s ≠ 0 := by
    simpa [XiPacket.t] using s.ht

  exact False.elim (ht_ne ht_zero)

#check Hyperlocal.Targets.XiPacket.rec2_wpAt_on_resonant32_closed

end XiPacket
end Targets
end Hyperlocal
