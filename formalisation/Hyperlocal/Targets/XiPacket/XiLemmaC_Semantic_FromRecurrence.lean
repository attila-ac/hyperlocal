/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_Semantic_FromRecurrence.lean

  Plan C++ frontier file: the *only remaining* Xi-dependent semantic deliverable.

  **Design goal:** keep *one* semantic cliff, but phrase it in the most
  implementation-friendly form.

  We therefore make the single axiom return the *RecOut* package:

      hb2 : bCoeff(…,2)=0
      hb3 : bCoeff(…,3)=0
      hRe : (Xi (sc s)).re ≠ 0

  Everything else is pure conversion:
    RecOut ⇒ Core ⇒ (hell2/hell3) and kappa≠0 ⇒ XiLemmaC_Semantic
-/

import Hyperlocal.Targets.XiPacket.XiLemmaC_SemanticToWindowPayload
import Hyperlocal.Targets.XiPacket.XiLemmaC_KappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Minimal “semantic output” we ultimately want from the ξ windowed recurrence/coupling. -/
structure XiLemmaC_RecOut (s : _root_.Hyperlocal.OffSeed Xi) : Prop where
  hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0
  hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0
  hRe : (Xi (sc s)).re ≠ 0

/--
RecOut ⇒ XiLemmaC_Semantic (pure conversion):
turn hb2/hb3 into hell2/hell3 using `XiLemmaC_hell{2,3}_of_core`,
and turn hRe into κ≠0 using `XiLemmaC_kappa_closedForm`.
-/
theorem XiLemmaC_Semantic_of_recOut
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_RecOut s) :
    XiLemmaC_Semantic s := by
  -- package hb2/hb3/hRe into the Core form used by the algebraic lemmas
  have hc : XiLemmaC_Core s :=
    { hb2   := h.hb2
      hb3   := h.hb3
      hkappa := by
        -- κ(...) = (Xi(sc)).re by closed form, so κ≠0 follows from hRe
        simpa [XiLemmaC_kappa_closedForm] using h.hRe }

  refine
    { hEll2 := XiLemmaC_hell2_of_core (s := s) hc
      hEll3 := XiLemmaC_hell3_of_core (s := s) hc
      hKap  := hc.hkappa }

/-- THE single remaining semantic cliff: ξ recurrence/coupling produces `RecOut`. -/
axiom xiLemmaC_RecOut_fromRecurrence
    (s : _root_.Hyperlocal.OffSeed Xi) : XiLemmaC_RecOut s

/-- Public API used downstream: semantic package for Lemma C (now derived, not axiomatized). -/
theorem xiLemmaC_Semantic_fromRecurrence
    (s : _root_.Hyperlocal.OffSeed Xi) : XiLemmaC_Semantic s := by
  exact XiLemmaC_Semantic_of_recOut (s := s) (xiLemmaC_RecOut_fromRecurrence (s := s))

end XiPacket
end Targets
end Hyperlocal
