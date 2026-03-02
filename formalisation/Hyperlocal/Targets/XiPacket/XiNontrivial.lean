/-
  Hyperlocal/Targets/XiPacket/XiNontrivial.lean

  Axiom-free, snapshot-robust nontriviality facts for the concrete Xi function
  `Hyperlocal.xi`.

  Key point:
    Hyperlocal.xi z := z * (z - 1) * completedRiemannZeta₀ z + 1
  so at z = 0 we get Xi 0 = 1, hence Xi is not identically zero.

  IMPORTANT:
  `Xi` is already declared in `XiWindowDefs.lean`, so we do not redeclare it here.
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Concrete evaluation: `Xi 0 = 1`. -/
theorem Xi_zero_eq_one : Xi 0 = 1 := by
  -- `Hyperlocal.xi 0 = 0*(0-1)*Λ₀(0) + 1 = 1`
  simp [Xi, Hyperlocal.xi]

/-- Nonvanishing witness: `Xi 0 ≠ 0`. -/
theorem Xi_zero_ne_zero : Xi 0 ≠ 0 := by
  simpa [Xi_zero_eq_one]

/-- `Xi` is not the zero function. -/
theorem Xi_not_identically_zero : ¬ (Xi = (fun _ : ℂ => 0)) := by
  intro h
  have : Xi 0 = 0 := by simpa [h]
  exact Xi_zero_ne_zero this

/-- Existential form: there exists a point where `Xi` is nonzero. -/
theorem exists_Xi_ne_zero : ∃ z : ℂ, Xi z ≠ 0 := by
  exact ⟨0, Xi_zero_ne_zero⟩

end XiPacket
end Targets
end Hyperlocal
