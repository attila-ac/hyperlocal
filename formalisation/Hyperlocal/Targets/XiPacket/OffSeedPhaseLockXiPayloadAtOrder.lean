/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayloadAtOrder.lean

  Stage-3 consumer (AXIOM-FREE mainline): `OffSeedPhaseLock ξ`.

  This file intentionally does **not** build a `WindowPayload` and does **not**
  go through `WindowPayloadFacts`.

  Instead:
  * sine equalities come directly from the recurrence-identity theorems at the
    chosen pivot order `m`,
  * κ ≠ 0 comes from the dslope-native JetPivot gate
    (`xiJetNonflat_dslope_exists` + `hkappaAt_of_dslopeIter_ne0`).

  This removes the last dependency on the legacy anchor-based real-part nonvanishing
  constructor path.

  2026-03-13 honest post-axiom state:
  * the downstream recurrence-identity theorems are now theorem-gated
  * therefore this stage-3 consumer can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
      [RouteAWcScalarProvider]
-/

import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic
import Hyperlocal.Targets.XiPacket.XiDslopeToKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityIm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXiPayloadAtOrder

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-! ### Small algebra: `bCoeff = 0` forces `sin(t log p) = 0` -/

lemma sin_eq_zero_of_bCoeff_eq_zero (σ t p : ℝ)
    (hb : bCoeff σ t p = 0) :
    Real.sin (t * Real.log p) = 0 := by
  have hb' : pSigma σ p * Real.sin (t * Real.log p) = 0 := by
    simpa [PrimeTrigPacket.bCoeff] using hb
  have hp : pSigma σ p ≠ 0 := by
    simpa [PrimeTrigPacket.pSigma] using (Real.exp_ne_zero (-σ * Real.log p))
  exact (mul_eq_zero.mp hb').resolve_left hp

/-! ### Stage-3 bridge: `OffSeedPhaseLock ξ` (dslope-native κ-gate) -/

theorem offSeedPhaseLock_Xi
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  classical

  let m : ℕ := Classical.choose (xiJetNonflat_dslope_exists (s := s))
  have hmDs : XiPacket.dslopeIterAt (m := m) (s := s) ≠ 0 :=
    Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

  have hKap :
      (kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  cases hKap with
  | inl hRe =>
      have hb :
          bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
          bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
        xiToeplitzRecurrenceIdentity_atOrder (m := m) (s := s) hRe

      have hsin2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
        simpa [XiPacket.t, XiPacket.σ] using
          (sin_eq_zero_of_bCoeff_eq_zero (σ := σ s) (t := t s) (p := (2 : ℝ))
            (hb := hb.1))

      have hsin3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
        simpa [XiPacket.t, XiPacket.σ] using
          (sin_eq_zero_of_bCoeff_eq_zero (σ := σ s) (t := t s) (p := (3 : ℝ))
            (hb := hb.2))

      refine ⟨kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)), hRe, ?_, ?_⟩
      · simpa [XiPacket.t] using hsin2
      · simpa [XiPacket.t] using hsin3

  | inr hIm =>
      have hb :
          bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
          bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
        xiToeplitzRecurrenceIdentity_atOrder_im (m := m) (s := s) hIm

      have hsin2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
        simpa [XiPacket.t, XiPacket.σ] using
          (sin_eq_zero_of_bCoeff_eq_zero (σ := σ s) (t := t s) (p := (2 : ℝ))
            (hb := hb.1))

      have hsin3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
        simpa [XiPacket.t, XiPacket.σ] using
          (sin_eq_zero_of_bCoeff_eq_zero (σ := σ s) (t := t s) (p := (3 : ℝ))
            (hb := hb.2))

      refine ⟨kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)), hIm, ?_, ?_⟩
      · simpa [XiPacket.t] using hsin2
      · simpa [XiPacket.t] using hsin3

end OffSeedPhaseLockXiPayloadAtOrder
end Targets
end Hyperlocal
