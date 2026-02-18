/-
  Hyperlocal/Targets/XiPacket/XiWindowPayloadFromRecurrenceAtOrder.lean

  Plan C++J (Jet Pivot): build a usable `WindowPayload` for ξ without any
  value-level anchor nonvanishing.

  Inputs (and only inputs):

  * Jet nonflatness at some order `m` (currently a single axiom):
      `xiJetNonflat_re_exists : ∃ m, Re(Ξ^{(m)}(sc s)) ≠ 0`.

  * AtOrder ℓ-output from the Toeplitz recurrence arm:
      `xiToeplitzEllOutAt_fromRecurrenceC : XiToeplitzEllOutAt m s`.

  Together with the closed-form κ-at-order identity, these yield κ≠0 at that
  same order, and hence a full `WindowPayload (σ s) (t s)` built from the
  jet-pivot windows `w0At/wp2At/wp3At`.

  Downstream Stage-3 uses only `WindowPayloadFacts`, so this removes the last
  consumer of the legacy value-level anchor axiom `xi_sc_re_ne_zero`.
-/

import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
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

/-- Build `WindowPayload` from AtOrder ℓ-output + κ≠0 at the same order. -/
def xiWindowPayloadAt_of_C
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (hEll2 : Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0)
    (hEll3 : Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0)
    (hKap  : Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
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
      hkappa := Or.inl hKap }

/-! ### Jet-pivot payload from the Route-B frontiers -/

/-- The chosen jet order (noncomputable) from `xiJetNonflat_re_exists`. -/
noncomputable def xiJetPivotOrder (s : Hyperlocal.OffSeed Xi) : ℕ :=
  Classical.choose (xiJetNonflat_re_exists (s := s))

/-- The defining nonflatness witness for `xiJetPivotOrder`. -/
theorem xiJetPivotOrder_spec (s : Hyperlocal.OffSeed Xi) :
    (((cderivIter (xiJetPivotOrder s) Xi) (sc s))).re ≠ 0 :=
  Classical.choose_spec (xiJetNonflat_re_exists (s := s))

/-- Full `WindowPayload` for ξ from the jet-pivot order and AtOrder ℓ-out. -/
def xiWindowPayload_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    WindowPayload (σ s) (t s) := by
  classical
  let m : ℕ := xiJetPivotOrder s
  have hmRe : (((cderivIter m Xi) (sc s))).re ≠ 0 := by
    simpa [m, xiJetPivotOrder] using xiJetPivotOrder_spec (s := s)

  have hKap :
      kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 :=
    hkappaAt_re_of_cderivRe_ne0 (m := m) (s := s) hmRe

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
