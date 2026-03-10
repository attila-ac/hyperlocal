/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_SemanticToWindowPayload.lean

  PURE CONVERSION (no ξ / Toeplitz semantics):

  If your ξ-recurrence/coupling provides:
    • ell(...) = 0 at p=2
    • ell(...) = 0 at p=3
    • κ(...) ≠ 0

  then we derive:
    bCoeff(2)=0, bCoeff(3)=0

  and assemble `WindowPayload` by the Phase-4 constructor.

  This file contains ZERO analytic / Toeplitz reasoning.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiLemmaB_TrigSplit
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa
import Hyperlocal.Targets.XiPacket.XiWindowPayloadConstructor
import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- A “semantic” package that ξ-recurrence/coupling can reasonably output. -/
structure XiLemmaC_Semantic (s : _root_.Hyperlocal.OffSeed Xi) : Prop where
  hEll2 :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hEll3 :
    ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0
  hKap :
    kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0

/-- `ell=0` at p=2 plus κ≠0 forces `bCoeff(...,2)=0` (pure rewriting). -/
theorem bCoeff_two_eq_zero_of_semantic
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Semantic s) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  set k : ℝ :=
    kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) with hkdef
  have hk : k ≠ 0 := by
    simpa [hkdef] using h.hKap

  have hmul :
      (bCoeff (σ s) (t s) (2 : ℝ)) * k = 0 := by
    simpa [hkdef, ell_wp2_eq_b_mul_kappa] using h.hEll2

  have hmul' := congrArg (fun x : ℝ => x * k⁻¹) hmul
  simpa [mul_assoc, hk] using hmul'

/-- `ell=0` at p=3 plus κ≠0 forces `bCoeff(...,3)=0` (pure rewriting). -/
theorem bCoeff_three_eq_zero_of_semantic
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Semantic s) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  set k : ℝ :=
    kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) with hkdef
  have hk : k ≠ 0 := by
    simpa [hkdef] using h.hKap

  have hmul :
      (bCoeff (σ s) (t s) (3 : ℝ)) * k = 0 := by
    simpa [hkdef, ell_wp3_eq_b_mul_kappa] using h.hEll3

  have hmul' := congrArg (fun x : ℝ => x * k⁻¹) hmul
  simpa [mul_assoc, hk] using hmul'

/-- Semantic ell/kappa facts ⇒ your exact Core package. -/
theorem XiLemmaC_core_of_semantic
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Semantic s) :
    XiLemmaC_Core s := by
  refine
    { hb2 := bCoeff_two_eq_zero_of_semantic (s := s) h
      hb3 := bCoeff_three_eq_zero_of_semantic (s := s) h
      hkappa := h.hKap }

/-- Semantic facts ⇒ `WindowPayload (σ s) (t s)` for the definitional ξ-windows. -/
def xiWindowPayload_of_semantic
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Semantic s) :
    WindowPayload (σ s) (t s) := by
  have hc : XiLemmaC_Core s := XiLemmaC_core_of_semantic (s := s) h
  refine
    windowPayload_mk_of_BC (σ := σ s) (t := t s)
      (w0 s) (wc s) (ws s) (wp2 s) (wp3 s)
      (hW2 := XiLemmaB_hw2 (s := s))
      (hW3 := XiLemmaB_hw3 (s := s))
      (hEll2 := XiLemmaC_hell2_of_core (s := s) hc)
      (hEll3 := XiLemmaC_hell3_of_core (s := s) hc)
      (hKap  := hc.hkappa)

/-- Smoke-test: semantic ell/kappa ⇒ κ≠0 ∧ sin(t log2)=0 ∧ sin(t log3)=0. -/
theorem xi_semantic_exists_kappa_sinlog2_sinlog3
    (s : _root_.Hyperlocal.OffSeed Xi) (h : XiLemmaC_Semantic s) :
    ∃ κ : ℝ, κ ≠ 0 ∧
      Real.sin (t s * Real.log (2 : ℝ)) = 0 ∧
      Real.sin (t s * Real.log (3 : ℝ)) = 0 := by
  let X : WindowPayload (σ s) (t s) := xiWindowPayload_of_semantic (s := s) h
  have hKapRe :
      kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0 := by
    simpa [X] using h.hKap
  simpa [X] using
    WindowPayload.exists_kappa_sinlog2_sinlog3 X hKapRe

end XiPacket
end Targets
end Hyperlocal
