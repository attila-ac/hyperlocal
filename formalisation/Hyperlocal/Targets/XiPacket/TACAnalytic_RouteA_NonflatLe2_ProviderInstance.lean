/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_RouteA_NonflatLe2_ProviderInstance.lean

  Front~NF (Route–A nonflatness ≤ 2): semantic provider instance.

  Installs:
      instance : TAC.RouteA_Jet3NonzeroAnchors

  No axioms.
  No sorry.
-/

import Hyperlocal.Targets.XiPacket.TACAnalytic_RouteA_NonflatLe2_Landing
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotNonvanishingAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcCoordsFromRouteAJetLeibniz

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

namespace TAC

/-! ### Small helpers -/

private lemma complex_ne_zero_of_re_or_im_ne_zero {z : ℂ} :
    z.re ≠ 0 ∨ z.im ≠ 0 → z ≠ 0 := by
  intro h hz
  rcases h with hRe | hIm
  · exact hRe (by simpa [hz])
  · exact hIm (by simpa [hz])

/-- Bridge: `w0At_apply_f0` but stated at index `0` (simp normal form in this repo). -/
private lemma w0At_apply_zero (m : ℕ) (s : OffSeed Xi) :
    (w0At m s) (0 : Fin 3) = (cderivIter m Xi) (sc s) := by
  simpa using (w0At_apply_f0 (m := m) (s := s))

/-- Route–E anchor alignment used throughout the repo: `TAC.z_w0At s = s.ρ`. -/
private theorem z_w0At_eq_rho (s : OffSeed Xi) : TAC.z_w0At s = s.ρ := by
  apply Complex.ext
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]

/-- At index `0`, `wpAt` agrees with `w0At` (because `wc 0 = ws 0 = 0`). -/
private lemma wpAt_apply_zero (m : ℕ) (s : OffSeed Xi) (p : ℕ) :
    (wpAt m s p) (0 : Fin 3) = (w0At m s) (0 : Fin 3) := by
  simp [wpAt, wc_eq_basis, ws_eq_basis, basisW3, e1, e2]

private lemma wp2At_apply_zero (m : ℕ) (s : OffSeed Xi) :
    (wp2At m s) (0 : Fin 3) = (w0At m s) (0 : Fin 3) := by
  simpa [wp2At] using (wpAt_apply_zero (m := m) (s := s) (p := 2))

private lemma wp3At_apply_zero (m : ℕ) (s : OffSeed Xi) :
    (wp3At m s) (0 : Fin 3) = (w0At m s) (0 : Fin 3) := by
  simpa [wp3At] using (wpAt_apply_zero (m := m) (s := s) (p := 3))

/-- Closed form: `wc(1)=1`. -/
private lemma wc_apply_one (s : OffSeed Xi) :
    (wc s) (1 : Fin 3) = (1 : ℂ) := by
  simp [wc_eq_basis, basisW3, e1, e2]

/-! ### Provider instance -/

instance (priority := 1000)
    [XiAtOrderSigmaProvider]
    [XiJetWindowIsJetAtOrderQuotProvider] :
    RouteA_Jet3NonzeroAnchors where

  nonzero_at_rho := by
    intro s
    classical
    let m : ℕ := xiJetPivot_m (s := s)

    have hm_or :
        (((cderivIter m Xi) (sc s))).re ≠ 0 ∨ (((cderivIter m Xi) (sc s))).im ≠ 0 := by
      simpa [m] using (xiJetPivot_m_spec_re_or_im (s := s))

    have hXi : (cderivIter m Xi) (sc s) ≠ 0 :=
      complex_ne_zero_of_re_or_im_ne_zero (z := (cderivIter m Xi) (sc s)) hm_or

    have hw0 : (w0At m s) (0 : Fin 3) ≠ 0 := by
      simpa [w0At_apply_zero (m := m) (s := s)] using hXi

    have Hjet : IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) :=
      XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)

    have hEq0 : w0At m s = jet3 (routeA_G s) (TAC.z_w0At s) :=
      window_eq_jet3_routeA_of_isJet3AtOrderQuot
        (m := m) (s := s) (z := TAC.z_w0At s) (w := w0At m s) Hjet

    have hEq : w0At m s = jet3 (routeA_G s) (s.ρ) := by
      simpa [z_w0At_eq_rho (s := s)] using hEq0

    refine ⟨(0 : Fin 3), ?_⟩
    -- avoid simp on w0At; safe here
    simpa [hEq] using hw0

  nonzero_at_conj_rho := by
    intro s
    classical
    let m : ℕ := xiJetPivot_m (s := s)

    have hm_or :
        (((cderivIter m Xi) (sc s))).re ≠ 0 ∨ (((cderivIter m Xi) (sc s))).im ≠ 0 := by
      simpa [m] using (xiJetPivot_m_spec_re_or_im (s := s))

    have hXi : (cderivIter m Xi) (sc s) ≠ 0 :=
      complex_ne_zero_of_re_or_im_ne_zero (z := (cderivIter m Xi) (sc s)) hm_or

    have hw0 : (w0At m s) (0 : Fin 3) ≠ 0 := by
      simpa [w0At_apply_zero (m := m) (s := s)] using hXi

    -- CRITICAL: no simp/simpa mentioning wp2At; do contradiction + congrArg
    have hwp2 : (wp2At m s) (0 : Fin 3) ≠ 0 := by
      intro h0
      apply hw0
      have h : (wp2At m s) (0 : Fin 3) = (w0At m s) (0 : Fin 3) :=
        wp2At_apply_zero (m := m) (s := s)
      -- from h0 and h, deduce w0At ... 0 = 0
      exact (h.symm.trans h0)

    have Hjet : IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) :=
      XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)

    have hCanon : wp2At m s = jet3 (routeA_G s) (TAC.z_wp2At s) :=
      window_eq_jet3_routeA_of_isJet3AtOrderQuot
        (m := m) (s := s) (z := TAC.z_wp2At s) (w := wp2At m s) Hjet

    -- Convert nonzero window coord to nonzero jet3 coord WITHOUT simp unfolding wp2At
    have hjet0 : (jet3 (routeA_G s) (TAC.z_wp2At s)) (0 : Fin 3) ≠ 0 := by
      intro hz0
      apply hwp2
      have h0 : (wp2At m s) (0 : Fin 3) = (jet3 (routeA_G s) (TAC.z_wp2At s)) (0 : Fin 3) := by
        -- congrArg on the function equality
        simpa using congrArg (fun f => f (0 : Fin 3)) hCanon
      exact h0.trans hz0

    -- Now rewrite the anchor to the semantic form (safe; no wp2At involved)
    have hjet0' : (jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)) (0 : Fin 3) ≠ 0 := by
      simpa [TAC.z_wp2At] using hjet0

    refine ⟨(0 : Fin 3), ?_⟩
    -- coord 0 of jet3 is the value; simp is safe here
    simpa [jet3] using hjet0'

  nonzero_at_one_sub_conj_rho := by
    intro s
    classical
    let m : ℕ := xiJetPivot_m (s := s)

    have hm_or :
        (((cderivIter m Xi) (sc s))).re ≠ 0 ∨ (((cderivIter m Xi) (sc s))).im ≠ 0 := by
      simpa [m] using (xiJetPivot_m_spec_re_or_im (s := s))

    have hXi : (cderivIter m Xi) (sc s) ≠ 0 :=
      complex_ne_zero_of_re_or_im_ne_zero (z := (cderivIter m Xi) (sc s)) hm_or

    have hw0 : (w0At m s) (0 : Fin 3) ≠ 0 := by
      simpa [w0At_apply_zero (m := m) (s := s)] using hXi

    -- CRITICAL: no simp/simpa mentioning wp3At; do contradiction + congrArg
    have hwp3 : (wp3At m s) (0 : Fin 3) ≠ 0 := by
      intro h0
      apply hw0
      have h : (wp3At m s) (0 : Fin 3) = (w0At m s) (0 : Fin 3) :=
        wp3At_apply_zero (m := m) (s := s)
      exact (h.symm.trans h0)

    have Hjet : IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) :=
      XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)

    have hCanon : wp3At m s = jet3 (routeA_G s) (TAC.z_wp3At s) :=
      window_eq_jet3_routeA_of_isJet3AtOrderQuot
        (m := m) (s := s) (z := TAC.z_wp3At s) (w := wp3At m s) Hjet

    have hjet0 : (jet3 (routeA_G s) (TAC.z_wp3At s)) (0 : Fin 3) ≠ 0 := by
      intro hz0
      apply hwp3
      have h0 : (wp3At m s) (0 : Fin 3) = (jet3 (routeA_G s) (TAC.z_wp3At s)) (0 : Fin 3) := by
        simpa using congrArg (fun f => f (0 : Fin 3)) hCanon
      exact h0.trans hz0

    have hjet0' : (jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)) (0 : Fin 3) ≠ 0 := by
      simpa [TAC.z_wp3At] using hjet0

    refine ⟨(0 : Fin 3), ?_⟩
    simpa [jet3] using hjet0'

  nonzero_at_one_sub_rho := by
    intro s
    classical
    have hwc1 : (wc s) (1 : Fin 3) = (1 : ℂ) := by
      simpa using (wc_apply_one (s := s))

    have hderiv : deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) := by
      calc
        deriv (routeA_G s) (1 - s.ρ)
            = (wc s) (1 : Fin 3) := by
                simpa using (JetQuotOp.wc_1_from_routeAJetPkg (s := s)).symm
        _ = (1 : ℂ) := hwc1

    refine ⟨(1 : Fin 3), ?_⟩
    -- coord 1 of jet3 is deriv; simp is safe here
    simpa [jet3, hderiv]

end TAC

end XiPacket
end Targets
end Hyperlocal
