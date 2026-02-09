/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceSemantics.lean

  Phase 3: Toeplitz/recurrence layer becomes theorematic once the minimal
  “recurrence injection” is provided.

  In this aggressive version:
    * NO `sorry` here.
    * The ONLY open semantics are the two axioms living in:
        XiToeplitzRecurrenceInject.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa   -- reVec3_wp2/wp3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject      -- hb2/hb3 axioms
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Kernel-level output: currently just SpanOut, extendable later. -/
structure XiToeplitzKernelOut (s : Hyperlocal.OffSeed Xi) : Prop
    extends toSpanOut : XiToeplitzSpanOut s

/-- Pure algebra: KernelOut gives EllOut (via SpanOut ⇒ EllOut). -/
theorem XiToeplitzEllOut_of_kernel (s : Hyperlocal.OffSeed Xi)
    (k : XiToeplitzKernelOut s) : XiToeplitzEllOut s :=
  XiToeplitzEllOut.of_spanOut (s := s) (k.toSpanOut)

--------------------------------------------------------------------------------
-- Deterministic closure: hb2/hb3 ⇒ explicit Span witnesses
--------------------------------------------------------------------------------

lemma xiToeplitz_span2_of_hb2 (s : Hyperlocal.OffSeed Xi)
    (hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0) :
    ∃ (α β : ℝ),
      reVec3 (wp2 s) = α • reVec3 (w0 s) + β • reVec3 (wc s) := by
  refine ⟨(1 : ℝ), aCoeff (σ s) (t s) (2 : ℝ), ?_⟩
  -- reVec3_wp2 : reVec3(wp2) = reVec3(w0) + a•reVec3(wc) + b•reVec3(ws)
  -- kill b-term using hb2, then rewrite as 1•w0 + a•wc
  simp [reVec3_wp2, hb2]

lemma xiToeplitz_span3_of_hb3 (s : Hyperlocal.OffSeed Xi)
    (hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0) :
    ∃ (α β : ℝ),
      reVec3 (wp3 s) = α • reVec3 (w0 s) + β • reVec3 (wc s) := by
  refine ⟨(1 : ℝ), aCoeff (σ s) (t s) (3 : ℝ), ?_⟩
  simp [reVec3_wp3, hb3]

--------------------------------------------------------------------------------
-- Phase 3 endpoint: kernel (theorematic; semantics isolated to 2 axioms)
--------------------------------------------------------------------------------

theorem xiToeplitzKernelOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzKernelOut s := by
  have hb2 : bCoeff (σ s) (t s) (2 : ℝ) = 0 :=
    xiToeplitz_hb2_fromRecurrence (s := s)
  have hb3 : bCoeff (σ s) (t s) (3 : ℝ) = 0 :=
    xiToeplitz_hb3_fromRecurrence (s := s)

  -- build the extended record by supplying `toSpanOut`
  refine ⟨⟨?_, ?_⟩⟩
  · exact xiToeplitz_span2_of_hb2 (s := s) hb2
  · exact xiToeplitz_span3_of_hb3 (s := s) hb3

end XiPacket
end Targets
end Hyperlocal
