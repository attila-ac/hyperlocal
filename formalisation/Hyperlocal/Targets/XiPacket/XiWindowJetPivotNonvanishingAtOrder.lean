/-
  Hyperlocal/Targets/XiPacket/XiWindowJetPivotNonvanishingAtOrder.lean

  FULL REPLACEMENT (Prop→Type safe, now that both constructors exist).

  Uses:
    * `xiJetNonflat_re_or_im` from XiWindowAnchorNonvanishing
    * constructors:
        xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
        xiWindowPayloadAtOrder_of_hb2hb3_cderivIm_ne0
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

/-- Alternative JetPivot target (imaginary part). -/
def XiJetNonvanishingIm (s : _root_.Hyperlocal.OffSeed Xi) : Prop :=
  ∃ m : ℕ, (((cderivIter m Xi) (sc s))).im ≠ 0

/-- Combined existence (Prop-packaged): there is some order where Re≠0 or Im≠0. -/
def XiJetPivotExists (s : _root_.Hyperlocal.OffSeed Xi) : Prop :=
  ∃ m : ℕ,
    (((cderivIter m Xi) (sc s))).re ≠ 0
    ∨ (((cderivIter m Xi) (sc s))).im ≠ 0

theorem xiJetPivot_exists_m_re_or_im (s : _root_.Hyperlocal.OffSeed Xi) : XiJetPivotExists s := by
  classical
  have h := xiJetNonflat_re_or_im (s := s)
  -- h : (∃ m, Re≠0) ∨ (∃ m, Im≠0)
  cases h with
  | inl hRe =>
      refine ⟨Classical.choose hRe, Or.inl (Classical.choose_spec hRe)⟩
  | inr hIm =>
      refine ⟨Classical.choose hIm, Or.inr (Classical.choose_spec hIm)⟩

/-- Chosen JetPivot order `m(s)`. -/
noncomputable def xiJetPivot_m (s : _root_.Hyperlocal.OffSeed Xi) : ℕ :=
by
  classical
  exact Classical.choose (xiJetPivot_exists_m_re_or_im (s := s))

/-- Spec at the chosen order: either Re≠0 or Im≠0. -/
theorem xiJetPivot_m_spec_re_or_im (s : _root_.Hyperlocal.OffSeed Xi) :
    (((cderivIter (xiJetPivot_m (s := s)) Xi) (sc s))).re ≠ 0
    ∨ (((cderivIter (xiJetPivot_m (s := s)) Xi) (sc s))).im ≠ 0 := by
  classical
  simpa [xiJetPivot_m] using
    (Classical.choose_spec (xiJetPivot_exists_m_re_or_im (s := s)))

/--
Build the payload at the chosen JetPivot order.

Prop→Type safe:
we use `by_cases` on the Re-branch and resolve Im via `Or.resolve_left`.
-/
noncomputable def xiWindowPayloadSigma_of_hb2hb3 (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    Σ m : ℕ, WindowPayload (σ s) (t s) :=
by
  classical
  refine ⟨xiJetPivot_m (s := s), ?_⟩
  have hOr := xiJetPivot_m_spec_re_or_im (s := s)
  by_cases hRe :
      (((cderivIter (xiJetPivot_m (s := s)) Xi) (sc s))).re ≠ 0
  · exact
      xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
        (m := xiJetPivot_m (s := s)) (s := s) hb2 hb3 hRe
  · have hIm :
        (((cderivIter (xiJetPivot_m (s := s)) Xi) (sc s))).im ≠ 0 :=
        Or.resolve_left hOr hRe
    exact
      xiWindowPayloadAtOrder_of_hb2hb3_cderivIm_ne0
        (m := xiJetPivot_m (s := s)) (s := s) hb2 hb3 hIm

/-- Convenience: forget the chosen order and keep only the payload. -/
noncomputable def xiWindowPayload_of_hb2hb3 (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    WindowPayload (σ s) (t s) :=
  (xiWindowPayloadSigma_of_hb2hb3 (s := s) hb2 hb3).2

end XiPacket
end Targets
end Hyperlocal
