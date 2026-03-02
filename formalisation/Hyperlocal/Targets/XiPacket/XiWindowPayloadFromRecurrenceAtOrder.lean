/-
  Hyperlocal/Targets/XiPacket/XiWindowPayloadFromRecurrenceAtOrder.lean

  Plan C++J (Jet Pivot): build a usable `WindowPayload` for ξ.

  AXIOM-FREE (dslope-native):

  * Choose the pivot order `m` from the theorem-level dslope witness
        `xiJetNonflat_dslope_exists`.

  * Obtain the κ-gate at the same order using
        `hkappaAt_of_dslopeIter_ne0` (in `XiDslopeToKappaAtOrder.lean`).

  * Obtain ℓ-output at the same order from the Toeplitz recurrence arm:
        `xiToeplitzEllOutAt_fromRecurrenceC`.

  This deletes the previous local shim axiom `xiJetNonflat_re_exists`.
-/

import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiDslopeToKappaAtOrder
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-! ### Jet-pivot `WindowPayload` constructor -/

/-- Definitional trig-split at p=2 for the jet-pivot ξ windows. -/
@[simp] lemma xiAt_hW2 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ∀ i : Fin 3,
      (wp2At m s) i = (w0At m s) i
        + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ((wc s) i))
        + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ((ws s) i)) := by
  intro i
  rfl

/-- Definitional trig-split at p=3 for the jet-pivot ξ windows. -/
@[simp] lemma xiAt_hW3 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    ∀ i : Fin 3,
      (wp3At m s) i = (w0At m s) i
        + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ((wc s) i))
        + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ((ws s) i)) := by
  intro i
  rfl

/-- Build `WindowPayload` from AtOrder ℓ-output + widened κ-witness at the same order. -/
def xiWindowPayloadAt_of_C
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hEll2 : Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0)
    (hEll3 : Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0)
    (hKap  :
      (Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0))
    : WindowPayload (σ s) (t s) := by
  refine
    { w0 := w0At m s
      wc := wc s
      ws := ws s
      wp2 := wp2At m s
      wp3 := wp3At m s
      hw2 := xiAt_hW2 (m := m) (s := s)
      hw3 := xiAt_hW3 (m := m) (s := s)
      hell2 := hEll2
      hell3 := hEll3
      hkappa := hKap }

/-! ### Jet-pivot payload from the Route-B frontiers (AXIOM-FREE path) -/

/-- The chosen jet order (noncomputable) from `xiJetNonflat_dslope_exists`. -/
noncomputable def xiJetPivotOrder (s : Hyperlocal.OffSeed Xi) : ℕ :=
  Classical.choose (xiJetNonflat_dslope_exists (s := s))

/-- The defining dslope nonflatness witness for `xiJetPivotOrder`. -/
theorem xiJetPivotOrder_spec (s : Hyperlocal.OffSeed Xi) :
    dslopeIterAt (m := xiJetPivotOrder s) (s := s) ≠ 0 :=
  Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

/-- Full `WindowPayload` for ξ from the dslope-chosen pivot order and AtOrder ℓ-out. -/
def xiWindowPayload_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    WindowPayload (σ s) (t s) := by
  classical
  let m : ℕ := xiJetPivotOrder s
  have hmDs : dslopeIterAt (m := m) (s := s) ≠ 0 := by
    simpa [m, xiJetPivotOrder] using xiJetPivotOrder_spec (s := s)

  have hKap :
      (kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  have hEllOut : XiToeplitzEllOutAt m s :=
    xiToeplitzEllOutAt_fromRecurrenceC (m := m) (s := s)

  exact
    xiWindowPayloadAt_of_C (m := m) (s := s)
      (hEll2 := hEllOut.hell2)
      (hEll3 := hEllOut.hell3)
      (hKap := hKap)

end XiPacket
end Targets
end Hyperlocal
