/-
  Hyperlocal/Targets/XiPacket/XiWindowKappaClosedFormAtOrder.lean

  Plan C++J (Jet Pivot): closed-form for κ built from the order-m transported jet.

  IMPORTANT FIX (Lean error you saw):
  `wc` and `ws` are (by construction) *real* windows (their imag parts vanish),
  so `imVec3 (wc s)` and `imVec3 (ws s)` are the zero columns and cannot be used
  as the fixed triangular block.

  The correct “imag pivot” statement keeps the *same* triangular block
  `reVec3(wc), reVec3(ws)` and only switches the first column to `imVec3(w0At m s)`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Targets.XiTransport

/-- Evaluate the order-m central jet at coordinate `f0`. -/
@[simp] lemma xiCentralJetAt_apply_f0 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    (xiCentralJetAt m s) f0 = (cderivIter m Xi) (sc s) := by
  -- `f0` is `⟨0, _⟩`, so `![a,b,c] f0 = a`.
  simp [xiCentralJetAt]

/-- Evaluate the order-m transported jet at coordinate `f0`. -/
lemma w0At_apply_f0 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    (w0At m s) f0 = (cderivIter m Xi) (sc s) := by
  have hfix :=
    xiTransportOp_n2_fin0 (s := s) (w := xiCentralJetAt m s)
  -- hfix : (XiTransportOp 2 s (xiCentralJetAt m s)) f0 = (xiCentralJetAt m s) f0
  simpa [w0At] using hfix.trans (xiCentralJetAt_apply_f0 (m := m) (s := s))

/--
With the fixed triangular block `uc = reVec3(wc)` and `us = reVec3(ws)`,
κ reads only the `f0` entry of the first column `u0`.
-/
lemma kappa_eq_u0_f0_generic (s : Hyperlocal.OffSeed Xi) (u0 : Fin 3 → ℝ) :
    Transport.kappa u0 (reVec3 (wc s)) (reVec3 (ws s)) = u0 f0 := by
  classical
  -- Expand κ = det[u0, uc, us] and compute the (uc,us) columns from wc/ws basis form.
  -- This collapses to the triangular determinant = u0 f0.
  simp [Transport.kappa, Transport.ell, Transport.colsMat, Transport.baseMat,
        Matrix.det_fin_three,
        wc_eq_basis, ws_eq_basis,
        reVec3, basisW3, f0, f2, e0, e1, e2]

/-- Closed form: κ at order `m` is the real part of the `m`-th derivative at `sc`. -/
theorem XiLemmaC_kappa_closedFormAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
      =
    ((cderivIter m Xi) (sc s)).re := by
  have hkappa :
      Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
        =
      (reVec3 (w0At m s)) f0 := by
    simpa using
      (kappa_eq_u0_f0_generic (s := s) (u0 := reVec3 (w0At m s)))

  have hw :
      (reVec3 (w0At m s)) f0 = ((cderivIter m Xi) (sc s)).re := by
    -- `reVec3 w f0 = (w f0).re`
    simpa [reVec3] using
      congrArg Complex.re (w0At_apply_f0 (m := m) (s := s))

  exact hkappa.trans hw

/--
Imag pivot (correct form):
κ built from the *imaginary* first column but the *same real triangular block*.

So κ at order `m` equals `Im(Ξ^{(m)}(sc))`.
-/
theorem XiLemmaC_kappa_closedFormAt_im (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
      =
    ((cderivIter m Xi) (sc s)).im := by
  have hkappa :
      Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
        =
      (imVec3 (w0At m s)) f0 := by
    simpa using
      (kappa_eq_u0_f0_generic (s := s) (u0 := imVec3 (w0At m s)))

  have hw :
      (imVec3 (w0At m s)) f0 = ((cderivIter m Xi) (sc s)).im := by
    -- `imVec3 w f0 = (w f0).im`
    simpa [imVec3] using
      congrArg Complex.im (w0At_apply_f0 (m := m) (s := s))

  exact hkappa.trans hw

end XiPacket
end Targets
end Hyperlocal
