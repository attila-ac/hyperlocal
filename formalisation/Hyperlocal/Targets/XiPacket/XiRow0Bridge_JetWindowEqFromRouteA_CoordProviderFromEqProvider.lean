/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_CoordProviderFromEqProvider.lean

  Build full `RouteAJetCoordProvider` from Eq-provider for w0/wp2/wp3 and
  from the tiny wc-only axiom boundary for wc.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

@[simp] lemma xiCentralJetAt_zero (s : OffSeed Xi) : xiCentralJetAt 0 s = xiCentralJet s := by
  ext i
  fin_cases i <;> simp [xiCentralJetAt, xiCentralJet, xiJet3At, cderivIter]

@[simp] lemma w0At_zero (s : OffSeed Xi) : w0At 0 s = w0 s := by
  ext i
  simp [w0At, w0, xiTransportedJet, xiCentralJetAt_zero]

@[simp] lemma wp2At_zero (s : OffSeed Xi) : wp2At 0 s = wp2 s := by
  ext i
  simp [wp2At, wpAt, wp2, w0At_zero]

@[simp] lemma wp3At_zero (s : OffSeed Xi) : wp3At 0 s = wp3 s := by
  ext i
  simp [wp3At, wpAt, wp3, w0At_zero]

private theorem z_w0At_eq_rho (s : OffSeed Xi) : TAC.z_w0At s = s.ρ := by
  apply Complex.ext
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]
  · simp [TAC.z_w0At, sc, σ, t, Hyperlocal.Targets.XiTransport.delta]

instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] : RouteAJetCoordProvider := by
  classical
  refine
    { w0_0 := ?_, w0_1 := ?_, w0_2 := ?_
      wc_0 := ?_, wc_1 := ?_, wc_2 := ?_
      wp2_0 := ?_, wp2_1 := ?_, wp2_2 := ?_
      wp3_0 := ?_, wp3_1 := ?_, wp3_2 := ?_
      w0At_0 := ?_, w0At_1 := ?_, w0At_2 := ?_
      wp2At_0 := ?_, wp2At_1 := ?_, wp2At_2 := ?_
      wp3At_0 := ?_, wp3At_1 := ?_, wp3At_2 := ?_ }

  ---------------------------------------------------------------------------
  -- w0 : from m = 0 pivot, align z_w0At = ρ
  ---------------------------------------------------------------------------
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).w0At_eq
    have hw' : w0 s = TAC.jet3 (routeA_G s) (TAC.z_w0At s) := by
      simpa [w0At_zero] using hw
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw'
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h0
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).w0At_eq
    have hw' : w0 s = TAC.jet3 (routeA_G s) (TAC.z_w0At s) := by
      simpa [w0At_zero] using hw
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw'
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h1
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).w0At_eq
    have hw' : w0 s = TAC.jet3 (routeA_G s) (TAC.z_w0At s) := by
      simpa [w0At_zero] using hw
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw'
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h2

  ---------------------------------------------------------------------------
  -- wc : tiny wc-only boundary
  ---------------------------------------------------------------------------
  · intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_0 s
  · intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_1 s
  · intro s
    simpa using RouteAJetCoordAxioms.Wc.ax_wc_2 s

  ---------------------------------------------------------------------------
  -- wp2 : from m = 0 pivot; z_wp2At simp
  ---------------------------------------------------------------------------
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp2At_eq
    have hw' : wp2 s = TAC.jet3 (routeA_G s) (TAC.z_wp2At s) := by
      simpa [wp2At_zero] using hw
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp2At] using h0
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp2At_eq
    have hw' : wp2 s = TAC.jet3 (routeA_G s) (TAC.z_wp2At s) := by
      simpa [wp2At_zero] using hw
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp2At] using h1
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp2At_eq
    have hw' : wp2 s = TAC.jet3 (routeA_G s) (TAC.z_wp2At s) := by
      simpa [wp2At_zero] using hw
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp2At] using h2

  ---------------------------------------------------------------------------
  -- wp3 : from m = 0 pivot; z_wp3At simp
  ---------------------------------------------------------------------------
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp3At_eq
    have hw' : wp3 s = TAC.jet3 (routeA_G s) (TAC.z_wp3At s) := by
      simpa [wp3At_zero] using hw
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp3At] using h0
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp3At_eq
    have hw' : wp3 s = TAC.jet3 (routeA_G s) (TAC.z_wp3At s) := by
      simpa [wp3At_zero] using hw
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp3At] using h1
  · intro s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot 0 s).wp3At_eq
    have hw' : wp3 s = TAC.jet3 (routeA_G s) (TAC.z_wp3At s) := by
      simpa [wp3At_zero] using hw
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw'
    simpa [TAC.jet3, TAC.z_wp3At] using h2

  ---------------------------------------------------------------------------
  -- w0At : direct from provider at m; align z_w0At = ρ
  ---------------------------------------------------------------------------
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).w0At_eq
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h0
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).w0At_eq
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h1
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).w0At_eq
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw
    simpa [TAC.jet3, z_w0At_eq_rho (s := s)] using h2

  ---------------------------------------------------------------------------
  -- wp2At : direct; z_wp2At simp
  ---------------------------------------------------------------------------
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp2At_eq
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp2At] using h0
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp2At_eq
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp2At] using h1
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp2At_eq
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp2At] using h2

  ---------------------------------------------------------------------------
  -- wp3At : direct; z_wp3At simp
  ---------------------------------------------------------------------------
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp3At_eq
    have h0 := congrArg (fun w => w ⟨0, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp3At] using h0
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp3At_eq
    have h1 := congrArg (fun w => w ⟨1, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp3At] using h1
  · intro m s
    have hw := (TAC.XiJetWindowEqAtOrderQuotProvider.windowEqAtOrderQuot m s).wp3At_eq
    have h2 := congrArg (fun w => w ⟨2, by decide⟩) hw
    simpa [TAC.jet3, TAC.z_wp3At] using h2

end XiPacket
end Targets
end Hyperlocal
