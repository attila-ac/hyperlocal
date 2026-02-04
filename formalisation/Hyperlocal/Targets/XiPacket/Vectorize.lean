/-
  Hyperlocal/Targets/XiPacket/Vectorize.lean

  Pure definitional helpers:
  Convert complex windows of length 3 into real vectors (Fin 3 → ℝ),
  and provide simp lemmas for linearity.
-/

import Hyperlocal.Transport.ToeplitzInterface
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/-- Real-part vectorisation of a complex length-3 window. -/
def reVec3 (w : Hyperlocal.Transport.Window 3) : Fin 3 → ℝ :=
  fun i => (w i).re

/-- Imag-part vectorisation of a complex length-3 window. -/
def imVec3 (w : Hyperlocal.Transport.Window 3) : Fin 3 → ℝ :=
  fun i => (w i).im

@[simp] lemma reVec3_add (w₁ w₂ : Hyperlocal.Transport.Window 3) :
    reVec3 (w₁ + w₂) = reVec3 w₁ + reVec3 w₂ := by
  funext i; simp [reVec3]

@[simp] lemma reVec3_smul (z : ℂ) (w : Hyperlocal.Transport.Window 3) :
    reVec3 (z • w) = fun i => ((z * w i).re) := by
  funext i; simp [reVec3]

end XiPacket
end Targets
end Hyperlocal
