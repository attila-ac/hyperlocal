/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayload.lean

  Build `OffSeedPhaseLock Xi` from `WindowPayloadFacts`.

  NOTE (2026-03-02):
  `WindowPayloadFacts` currently requires a *Re-κ* witness

      kappa (reVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0

  while the new dslope-native jet pivot produces only an Or-witness
  (Re-κ ≠ 0 ∨ Im-κ ≠ 0).  Until the PhaseLock consumer is widened to accept
  the Or-witness, we build the packet at order `m = 0` using the legacy
  anchor nonvanishing axiom from `XiWindowScNonvanishing`.

  This file does NOT use the deleted shim `xiJetNonflat_re_exists` and does NOT
  reference `hkappaAt_re_of_cderivRe_ne0`.
-/

import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Targets.RiemannXi

import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowPayloadFromRecurrenceAtOrder  -- xiWindowPayloadAt_of_C
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder        -- κ closed form at order m
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing               -- xi_sc_re_ne_zero (axiom)

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXiPayload

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Targets.XiPacket

/--
Re-κ witness at order `m = 0`, in the exact shape required by `WindowPayloadFacts`.

Key point: avoid `simp [hk]` against the κ closed form (it expands `wc/ws` to basis form).
Instead use a `calc` chain so `hk` matches *definitionally*.
-/
theorem kappa_re_ne0_atOrder0 (s : Hyperlocal.OffSeed Xi) :
    kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
  intro hk
  -- κ=0 ⇒ Re(cderivIter 0 Xi (sc s))=0 via the closed form (no simp-unfold of wc/ws here).
  have hRe0 : ((cderivIter 0 Xi) (sc s)).re = 0 := by
    calc
      ((cderivIter 0 Xi) (sc s)).re
          =
        kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
          simpa using (XiLemmaC_kappa_closedFormAt (m := (0 : ℕ)) (s := s)).symm
      _ = 0 := hk

  -- Now contradict the legacy anchor axiom.
  -- We *allow* simp to unfold `cderivIter` and `Xi` to match the axiom’s statement.
  have : (Xi (sc s)).re = 0 := by
    -- `cderivIter 0 Xi = Xi` definitionally in your development.
    simpa [cderivIter] using hRe0

  exact xi_sc_re_ne_zero (s := s) this

/-- Build a `WindowPayload` for ξ at order `m = 0` (PhaseLock consumer wants Re-κ). -/
def xiWindowPayload_of_window (s : Hyperlocal.OffSeed Xi) :
    WindowPayload (σ s) (t s) := by
  classical
  let m : ℕ := 0

  -- ℓ-output at order 0 from the recurrence arm
  have hEllOut : XiToeplitzEllOutAt m s :=
    xiToeplitzEllOutAt_fromRecurrenceC (m := m) (s := s)

  have hKapRe :
      kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
    simpa [m] using (kappa_re_ne0_atOrder0 (s := s))

  exact
    xiWindowPayloadAt_of_C (m := m) (s := s)
      (hEll2 := hEllOut.hell2)
      (hEll3 := hEllOut.hell3)
      (hKap := Or.inl hKapRe)

/--
Main deliverable for the Stage-3 bridge:
`OffSeedPhaseLock ξ` obtained purely from `WindowPayloadFacts`.
-/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  let X : WindowPayload (σ s) (t s) := xiWindowPayload_of_window (s := s)

  -- Re-κ witness in the exact shape expected by `WindowPayloadFacts`.
  have hKapRe :
      kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0 := by
    -- unfold `X` and reuse the order-0 lemma; avoids any fragile `simp` through the payload record.
    simpa [X, xiWindowPayload_of_window, xiWindowPayloadAt_of_C] using
      (kappa_re_ne0_atOrder0 (s := s))

  -- Discharge PhaseLock via `WindowPayloadFacts`.
  simpa [XiPacket.t, XiPacket.σ, X] using
    (WindowPayload.exists_kappa_sinlog2_sinlog3 (X := X) (hKapRe := hKapRe))

end OffSeedPhaseLockXiPayload
end Targets
end Hyperlocal
