/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceSemantics.lean

  Phase 3: Toeplitz/recurrence layer becomes theorematic once the minimal
  “recurrence injection” is provided.

  In this aggressive version:
    * NO `sorry` here.
    * The ONLY open semantics are the two axioms living in:
        XiToeplitzRecurrenceInject.lean

  2026-03-13 honest post-axiom state:
  * the recurrence injection boundary is now theorem-gated
  * therefore the downstream semantics endpoint can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Kernel-level output: currently just SpanOut, extendable later. -/
structure XiToeplitzKernelOut (s : Hyperlocal.OffSeed Xi) : Prop
    extends toSpanOut : XiToeplitzSpanOut s

/-- Pure algebra: KernelOut gives EllOut (via SpanOut ⇒ EllOut). -/
theorem XiToeplitzEllOut_of_kernel
    (s : Hyperlocal.OffSeed Xi)
    (k : XiToeplitzKernelOut s) :
    XiToeplitzEllOut s :=
  XiToeplitzEllOut.of_spanOut (s := s) (k.toSpanOut)

--------------------------------------------------------------------------------
-- Deterministic closure: hb2/hb3 ⇒ explicit Span witnesses
--------------------------------------------------------------------------------

lemma xiToeplitz_span2_of_hb2
    (s : Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0) :
    ∃ (α β : ℝ),
      reVec3 (wp2 s) = α • reVec3 (w0 s) + β • reVec3 (wc s) := by
  refine ⟨(1 : ℝ), aCoeff (σ s) (t s) (2 : ℝ), ?_⟩
  simp [reVec3_wp2, hb2]

lemma xiToeplitz_span3_of_hb3
    (s : Hyperlocal.OffSeed Xi)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    ∃ (α β : ℝ),
      reVec3 (wp3 s) = α • reVec3 (w0 s) + β • reVec3 (wc s) := by
  refine ⟨(1 : ℝ), aCoeff (σ s) (t s) (3 : ℝ), ?_⟩
  simp [reVec3_wp3, hb3]

--------------------------------------------------------------------------------
-- Phase 3 endpoint: kernel (theorematic; semantics isolated to 2 axioms)
--------------------------------------------------------------------------------

theorem xiToeplitzKernelOut_fromRecurrence
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiToeplitzKernelOut s := by
  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
    xiToeplitz_hb2_fromRecurrence (s := s)
  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
    xiToeplitz_hb3_fromRecurrence (s := s)

  refine ⟨⟨?_, ?_⟩⟩
  · exact xiToeplitz_span2_of_hb2 (s := s) hb2
  · exact xiToeplitz_span3_of_hb3 (s := s) hb3

end XiPacket
end Targets
end Hyperlocal
