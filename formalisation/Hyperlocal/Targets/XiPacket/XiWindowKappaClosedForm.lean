/-
  Hyperlocal/Targets/XiPacket/XiWindowKappaClosedForm.lean

  Pure Toeplitz/shift-generated computation:
    κ(reVec3 w0, reVec3 wc, reVec3 ws) = (Xi (sc s)).re

  This file is intentionally κ-only.  It does NOT mention JetQuotOp or any
  Route-B row-0 jet-quotient identities.  Those belong in the jet-quotient
  semantic gate layer.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.XiWindowBasisSimp
import Hyperlocal.Transport.PrimeSineRescue
import Hyperlocal.Targets.XiTransportOp
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Targets.XiTransport

/-- `XiWindowDefs` only gives `e1,e2`; add `e0` locally. -/
abbrev e0 : Fin 3 := ⟨0, by decide⟩

/-- Convenience numerals for `Fin 3`. -/
abbrev f0 : Fin 3 := e0
abbrev f1 : Fin 3 := e1
abbrev f2 : Fin 3 := e2

/-- `xiCentralJet` really is `![Xi z, Xi' z, Xi'' z]`, so at index 0 it is `Xi z`. -/
@[simp] lemma xiCentralJet_apply_f0 (s : Hyperlocal.OffSeed Xi) :
    xiCentralJet s f0 = Xi (sc s) := by
  simp [xiCentralJet, xiJet3At, f0, e0]

/-
  The three Toeplitz computations at n=2.

  Key point: unfold `e1/e2` (or use `f1/f2`) so simp can decide Fin equalities.
-/

/-- On `basisW3 e2`, every positive right-shift term vanishes, so transport fixes it. -/
lemma xiTransportOp_n2_basis2 (s : Hyperlocal.OffSeed Xi) :
    XiTransport.XiTransportOp 2 s (basisW3 e2) = basisW3 e2 := by
  ext i
  fin_cases i <;>
    simp [XiTransport.XiTransportOp, XiTransport.shiftCoeff, XiTransport.delta,
      Transport.toeplitzR, Transport.shiftCombo, Transport.compPow,
      Transport.shiftRₗ_apply, Finset.sum_range_succ,
      basisW3, e2]

/-- On `basisW3 e1`, only shifts k=0,1 survive in a 3-window, so `e1 ↦ e1 + δ·e2`. -/
lemma xiTransportOp_n2_basis1 (s : Hyperlocal.OffSeed Xi) :
    XiTransport.XiTransportOp 2 s (basisW3 e1)
      = basisW3 e1 + (XiTransport.delta s : ℂ) • (basisW3 e2) := by
  ext i
  fin_cases i <;>
    simp [XiTransport.XiTransportOp, XiTransport.shiftCoeff, XiTransport.delta,
      Transport.toeplitzR, Transport.shiftCombo, Transport.compPow,
      Transport.shiftRₗ_apply, Finset.sum_range_succ,
      basisW3, e1, e2]

/-- At index `0`, every positive right-shift term contributes `0`, so Toeplitz fixes coord `0`. -/
lemma xiTransportOp_n2_fin0 (s : Hyperlocal.OffSeed Xi) (w : Transport.Window 3) :
    (XiTransport.XiTransportOp 2 s w) f0 = w f0 := by
  simp [XiTransport.XiTransportOp, XiTransport.shiftCoeff, XiTransport.delta,
    Transport.toeplitzR, Transport.shiftCombo, Transport.compPow,
    Transport.shiftRₗ_apply, Transport.shiftR'_zero,
    Finset.sum_range_succ, f0, e0]

/-- `ws` is transport of basis `e2`, and at n=2 it is fixed. -/
@[simp] lemma ws_eq_basis (s : Hyperlocal.OffSeed Xi) :
    ws s = basisW3 e2 := by
  simpa [ws] using (xiTransportOp_n2_basis2 (s := s))

/-- `wc` is transport of basis `e1`, giving the closed form `e1 + δ·e2`. -/
@[simp] lemma wc_eq_basis (s : Hyperlocal.OffSeed Xi) :
    wc s = basisW3 e1 + (XiTransport.delta s : ℂ) • basisW3 e2 := by
  simpa [wc] using (xiTransportOp_n2_basis1 (s := s))

/-- At index `0`, `w0` evaluates to `Xi(sc s)` because Toeplitz fixes coordinate `0`. -/
lemma w0_apply_f0 (s : Hyperlocal.OffSeed Xi) : (w0 s) f0 = Xi (sc s) := by
  have hfix := xiTransportOp_n2_fin0 (s := s) (w := xiCentralJet s)
  simpa [w0, xiTransportedJet, f0, e0] using hfix.trans (xiCentralJet_apply_f0 (s := s))

/--
With `uc = reVec3(wc)` and `us = reVec3(ws)` the determinant defining κ is
lower-triangular with diagonal entries `(u0 0), 1, 1`. Hence κ = u0 0.
-/
lemma kappa_eq_u0_f0 (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
      = (reVec3 (w0 s)) f0 := by
  classical
  set u0 : Fin 3 → ℝ := reVec3 (w0 s)
  set uc : Fin 3 → ℝ := reVec3 (wc s)
  set us : Fin 3 → ℝ := reVec3 (ws s)

  have h_uc0 : uc f0 = 0 := by
    simp [uc, wc_eq_basis, reVec3, basisW3, f0, f1, f2, e0, e1, e2]
  have h_uc1 : uc f1 = 1 := by
    simp [uc, wc_eq_basis, reVec3, basisW3, f0, f1, f2, e0, e1, e2]
  have h_uc2 : uc f2 = XiTransport.delta s := by
    simp [uc, wc_eq_basis, reVec3, basisW3, f0, f1, f2, e0, e1, e2]

  have h_us0 : us f0 = 0 := by
    simp [us, ws_eq_basis, reVec3, basisW3, f0, f1, f2, e0, e2]
  have h_us1 : us f1 = 0 := by
    simp [us, ws_eq_basis, reVec3, basisW3, f0, f1, f2, e1, e2]
  have h_us2 : us f2 = 1 := by
    simp [us, ws_eq_basis, reVec3, basisW3, f0, f1, f2, e2]

  simp [Transport.kappa, Transport.ell, Transport.colsMat, Transport.baseMat,
    Matrix.det_fin_three,
    u0, uc, us,
    h_uc0, h_uc1, h_uc2, h_us0, h_us1, h_us2,
    reVec3, basisW3, f0, f1, f2, e0, e1, e2]

/-- **Closed form**: κ for the definitional ξ-windows equals `Re(Xi(sc))`. -/
theorem XiLemmaC_kappa_closedForm (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
      = (Xi (sc s)).re := by
  have hk :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (reVec3 (w0 s)) f0 :=
    kappa_eq_u0_f0 (s := s)
  have hw : (reVec3 (w0 s)) f0 = (Xi (sc s)).re := by
    simpa [reVec3, f0, e0] using congrArg Complex.re (w0_apply_f0 (s := s))
  exact hk.trans hw

end XiPacket
end Targets
end Hyperlocal
