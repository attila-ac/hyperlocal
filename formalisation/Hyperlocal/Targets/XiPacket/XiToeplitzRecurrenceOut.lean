/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceOut.lean

  Toeplitz/recurrence extraction layer (axiom-free).

  Goal: keep this file purely algebraic/definitional:
  * define the “span-output” contract (what concrete Toeplitz extraction should provide)
  * define the downstream “ell-output” contract (what Lemma-C plumbing needs)
  * prove: SpanOut ⇒ EllOut using multilinearity of det in the 3rd column

  The FINAL semantic cliff (SpanOut from ξ Toeplitz/recurrence) lives in:
    Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/-- Concrete Toeplitz extraction output (bridge contract):

The prime windows `wp2/wp3` lie in the ℝ-span of `{w0,wc}` at the real-vector level. -/
structure XiToeplitzSpanOut (s : Hyperlocal.OffSeed Xi) : Prop where
  hspan2 : ∃ (α β : ℝ),
    reVec3 (wp2 s) = α • reVec3 (w0 s) + β • reVec3 (wc s)
  hspan3 : ∃ (α β : ℝ),
    reVec3 (wp3 s) = α • reVec3 (w0 s) + β • reVec3 (wc s)

/-- What the Lemma-C pipeline needs: the two ℓ-vanishings. -/
structure XiToeplitzEllOut (s : Hyperlocal.OffSeed Xi) : Prop where
  hell2 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0
  hell3 :
    Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0

namespace XiToeplitzEllOut

/-- Span-output implies ℓ-vanishing by multilinearity of det in the 3rd column. -/
theorem of_spanOut (s : Hyperlocal.OffSeed Xi) (h : XiToeplitzSpanOut s) :
    XiToeplitzEllOut s := by
  refine ⟨?_, ?_⟩
  · obtain ⟨α, β, hlin⟩ := h.hspan2
    set u0 : Fin 3 → ℝ := reVec3 (w0 s)
    set uc : Fin 3 → ℝ := reVec3 (wc s)
    have hlin' : reVec3 (wp2 s) = α • u0 + β • uc := by
      simpa [u0, uc] using hlin
    have hzero : Transport.ell u0 uc (reVec3 (wp2 s)) = 0 := by
      calc
        Transport.ell u0 uc (reVec3 (wp2 s))
            = Transport.ell u0 uc (α • u0 + β • uc) := by
                simpa [hlin']
        _ = Transport.ell u0 uc (α • u0) + Transport.ell u0 uc (β • uc) := by
                simpa using (Transport.ell_add u0 uc (α • u0) (β • uc))
        _ = (α * Transport.ell u0 uc u0) + (β * Transport.ell u0 uc uc) := by
                simp [Transport.ell_smul]
        _ = 0 := by
                simp [Transport.ell_u0, Transport.ell_uc]
    simpa [u0, uc] using hzero
  · obtain ⟨α, β, hlin⟩ := h.hspan3
    set u0 : Fin 3 → ℝ := reVec3 (w0 s)
    set uc : Fin 3 → ℝ := reVec3 (wc s)
    have hlin' : reVec3 (wp3 s) = α • u0 + β • uc := by
      simpa [u0, uc] using hlin
    have hzero : Transport.ell u0 uc (reVec3 (wp3 s)) = 0 := by
      calc
        Transport.ell u0 uc (reVec3 (wp3 s))
            = Transport.ell u0 uc (α • u0 + β • uc) := by
                simpa [hlin']
        _ = Transport.ell u0 uc (α • u0) + Transport.ell u0 uc (β • uc) := by
                simpa using (Transport.ell_add u0 uc (α • u0) (β • uc))
        _ = (α * Transport.ell u0 uc u0) + (β * Transport.ell u0 uc uc) := by
                simp [Transport.ell_smul]
        _ = 0 := by
                simp [Transport.ell_u0, Transport.ell_uc]
    simpa [u0, uc] using hzero

end XiToeplitzEllOut

end XiPacket
end Targets
end Hyperlocal
