/-
  Hyperlocal/Targets/XiPacket/XiWindowKappaClosedFormAtOrder.lean

  Plan C++J (Jet Pivot): closed-form for κ built from the order-m transported jet.
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
With `uc = reVec3(wc)` and `us = reVec3(ws)` fixed (triangular block),
κ reads only the `f0` entry of the `u0` column.
-/
lemma kappa_eq_u0_f0_generic (s : Hyperlocal.OffSeed Xi) (u0 : Fin 3 → ℝ) :
    Transport.kappa u0 (reVec3 (wc s)) (reVec3 (ws s)) = u0 f0 := by
  classical
  -- Expand κ = det[u0, uc, us] and compute the (uc,us) columns from wc/ws basis form.
  -- This collapses to the triangular determinant = u0 f0.
  simp [Transport.kappa, Transport.ell, Transport.colsMat, Transport.baseMat,
        Matrix.det_fin_three,
        wc_eq_basis, ws_eq_basis,
        reVec3, basisW3, f0, f1, f2, e0, e1, e2]

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

end XiPacket
end Targets
end Hyperlocal
