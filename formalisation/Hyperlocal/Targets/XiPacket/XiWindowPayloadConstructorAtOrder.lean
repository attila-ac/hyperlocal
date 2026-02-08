/-
  Hyperlocal/Targets/XiPacket/XiWindowPayloadConstructorAtOrder.lean

  Plan C++J (Jet Pivot): Phase-4 payload constructor “at order m”.

  This is intentionally cheap: just record construction of `WindowPayload`
  using definitional jet windows
      w0At m s, wp2At m s, wp3At m s
  and the Move-2 core ⇒ (hell2At, hell3At) lemmas.

  No semantic proofs here.
-/

import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
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

/-- Definitional trig-split for `wp2At`. -/
@[simp] lemma xi_hW2At (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi) :
    ∀ i,
      wp2At m s i
        =
      w0At m s i
        + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * wc s i)
        + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * ws s i) := by
  intro i
  rfl

/-- Definitional trig-split for `wp3At`. -/
@[simp] lemma xi_hW3At (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi) :
    ∀ i,
      wp3At m s i
        =
      w0At m s i
        + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * wc s i)
        + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * ws s i) := by
  intro i
  rfl

/--
Phase-4 payload constructor at order `m`, fed by the “AtOrder Lemma-C core” package.
-/
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

/--
Convenience: build the order-`m` payload from `(hb2,hb3)` plus the JetPivot nonvanishing witness
`Re(Ξ^{(m)}(sc)) ≠ 0`, using `hkappaAt_of_cderivRe_ne0`.
-/
def xiWindowPayloadAtOrder_of_hb2hb3_cderivRe_ne0
    (m : ℕ) (s : _root_.Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0)
    (hRe : (((cderivIter m Xi) (sc s))).re ≠ 0) :
    WindowPayload (σ s) (t s) :=
by
  refine xiWindowPayloadAtOrder_of_core (m := m) (s := s) ?_
  refine
    { hb2 := hb2
      hb3 := hb3
      hkappaAt := hkappaAt_of_cderivRe_ne0 (m := m) (s := s) hRe }

end XiPacket
end Targets
end Hyperlocal
