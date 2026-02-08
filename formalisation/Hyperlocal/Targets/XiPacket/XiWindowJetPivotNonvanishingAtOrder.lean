/-
  Hyperlocal/Targets/XiPacket/XiWindowJetPivotNonvanishingAtOrder.lean

  Plan C++J (Jet Pivot): isolate the ONLY remaining analytic nonvanishing input:

    ∃ m, Re(Ξ^{(m)}(sc s)) ≠ 0

  and then choose such an order `m(s)` and build the order-m payload from:
    • hb2, hb3  (from recurrence side; independent of m)
    • the chosen witness hRe at order m(s)
  via `xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0`.

  For now this is bridged from the existing anchor axiom (take m=0),
  so NO new axioms are added.
-/

import Hyperlocal.Targets.XiPacket.XiWindowPayloadConstructorAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- JetPivot semantic target: some order has nonzero real part at the anchor `sc`. -/
def XiJetNonvanishing (s : _root_.Hyperlocal.OffSeed Xi) : Prop :=
  ∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0

/--
Temporary bridge (NO new axiom):
derive JetPivot nonvanishing from the existing Plan-C++ anchor axiom by taking `m = 0`.
Delete this bridge once you prove JetPivot nonvanishing directly.
-/
theorem xiJetPivot_exists_cderivRe_ne0 (s : _root_.Hyperlocal.OffSeed Xi) :
    ∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0 := by
  refine ⟨0, ?_⟩
  -- `cderivIter 0 Xi = Xi`
  simpa [cderivIter] using (xi_sc_re_ne_zero (s := s))

/-- Chosen JetPivot order `m(s)`. -/
noncomputable def xiJetPivot_m (s : _root_.Hyperlocal.OffSeed Xi) : ℕ :=
  Classical.choose (xiJetPivot_exists_cderivRe_ne0 (s := s))

/-- The defining witness: `Re(Ξ^{(m(s))}(sc s)) ≠ 0`. -/
theorem xiJetPivot_m_spec (s : _root_.Hyperlocal.OffSeed Xi) :
    (((cderivIter (xiJetPivot_m (s := s)) Xi) (sc s))).re ≠ 0 := by
  simpa [xiJetPivot_m] using
    (Classical.choose_spec (xiJetPivot_exists_cderivRe_ne0 (s := s)))

/--
Build the payload at the chosen JetPivot order, keeping the order as a Σ-type.
-/
noncomputable def xiWindowPayloadSigma_of_hb2hb3 (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    Σ m : ℕ, WindowPayload (σ s) (t s) :=
by
  refine ⟨xiJetPivot_m (s := s), ?_⟩
  exact
    xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
      (m := xiJetPivot_m (s := s)) (s := s)
      hb2 hb3 (xiJetPivot_m_spec (s := s))

/-- Convenience: forget the chosen order and keep only the payload. -/
noncomputable def xiWindowPayload_of_hb2hb3 (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    WindowPayload (σ s) (t s) :=
  (xiWindowPayloadSigma_of_hb2hb3 (s := s) hb2 hb3).2

end XiPacket
end Targets
end Hyperlocal
