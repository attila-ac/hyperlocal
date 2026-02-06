/-
  Hyperlocal/Targets/XiPacket/XiLemmaB_TrigSplit.lean

  Phase 3B: Lemma B (Trig split) for definitional ξ-windows from XiWindowDefs.

  Design choice (Plan C++):
    If wp2/wp3 are defined in XiWindowDefs by the trig-split formula,
    then Lemma B is a tiny proof (rfl).
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket

/-- Lemma B at p=2: pointwise trig-split identity for the definitional window `wp2`. -/
theorem XiLemmaB_hw2 (s : Hyperlocal.OffSeed Hyperlocal.xi) :
    ∀ i : Fin 3,
      (wp2 s) i =
        (w0 s) i
        + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (wc s) i)
        + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (ws s) i) := by
  intro i
  rfl

/-- Lemma B at p=3: pointwise trig-split identity for the definitional window `wp3`. -/
theorem XiLemmaB_hw3 (s : Hyperlocal.OffSeed Hyperlocal.xi) :
    ∀ i : Fin 3,
      (wp3 s) i =
        (w0 s) i
        + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (wc s) i)
        + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (ws s) i) := by
  intro i
  rfl

end XiPacket
end Targets
end Hyperlocal
