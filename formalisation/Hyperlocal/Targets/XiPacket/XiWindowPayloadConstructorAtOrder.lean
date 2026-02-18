/-  Phase-4 payload constructor at order `m` (supports BOTH Re/Im JetPivot branches). -/

import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

@[simp] lemma xi_hW2At (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi) :
    ∀ i,
      wp2At m s i
        =
      w0At m s i
        + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * wc s i)
        + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ws s i) := by
  intro i; rfl

@[simp] lemma xi_hW3At (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi) :
    ∀ i,
      wp3At m s i
        =
      w0At m s i
        + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * wc s i)
        + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ws s i) := by
  intro i; rfl

def xiWindowPayloadAtOrder_of_core (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi)
    (h : XiLemmaC_CoreAt m s) :
    WindowPayload (σ s) (t s) :=
by
  refine
    { w0    := w0At m s
      wc    := wc s
      ws    := ws s
      wp2   := wp2At m s
      wp3   := wp3At m s
      hw2   := xi_hW2At (m := m) (s := s)
      hw3   := xi_hW3At (m := m) (s := s)
      hell2 := XiLemmaC_hell2At_of_core (m := m) (s := s) h
      hell3 := XiLemmaC_hell3At_of_core (m := m) (s := s) h
      hkappa := h.hkappaAt }

def xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
    (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0)
    (hRe : (((cderivIter m Xi) (sc s))).re ≠ 0) :
    WindowPayload (σ s) (t s) :=
by
  refine xiWindowPayloadAtOrder_of_core (m := m) (s := s) ?_
  refine { hb2 := hb2, hb3 := hb3, hkappaAt := hkappaAt_of_cderivRe_ne0 (m := m) (s := s) hRe }

def xiWindowPayloadAtOrder_of_hb2hb3_cderivIm_ne0
    (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0)
    (hIm : (((cderivIter m Xi) (sc s))).im ≠ 0) :
    WindowPayload (σ s) (t s) :=
by
  refine xiWindowPayloadAtOrder_of_core (m := m) (s := s) ?_
  refine { hb2 := hb2, hb3 := hb3, hkappaAt := hkappaAt_of_cderivIm_ne0 (m := m) (s := s) hIm }

theorem exists_xiWindowPayloadAtOrder_of_hb2hb3
    (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    ∃ m : ℕ, Nonempty (WindowPayload (σ s) (t s)) := by
  have h := xiJetNonflat_re_or_im (s := s)
  cases h with
  | inl hRe =>
      rcases hRe with ⟨m, hm⟩
      refine ⟨m, ⟨xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
        (m := m) (s := s) (hb2 := hb2) (hb3 := hb3) (hRe := hm)⟩⟩
  | inr hIm =>
      rcases hIm with ⟨m, hm⟩
      refine ⟨m, ⟨xiWindowPayloadAtOrder_of_hb2hb3_cderivIm_ne0
        (m := m) (s := s) (hb2 := hb2) (hb3 := hb3) (hIm := hm)⟩⟩


end XiPacket
end Targets
end Hyperlocal
