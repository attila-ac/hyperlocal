import Mathlib.NumberTheory.LSeries.RiemannZeta
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Factorization

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Factorization

/-!
  FE-only bridge for xi.

  IMPORTANT:
  In this repo the target function is `Hyperlocal.xi`.
-/

private abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Mathlib FE for the completed zeta. -/
theorem completedRiemannZeta_FE (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  simpa using (completedRiemannZeta_one_sub (s := s))

/-- **FE**: `xi s = xi (1 - s)` in your `FunFE` convention. -/
theorem Xi_FE : FunFE Xi := by
  intro s
  -- unfold your project's xi definition
  dsimp [Xi, Hyperlocal.xi]
  -- your goal is in terms of `oneMinus`; normalize it first
  simp [oneMinus]  -- turns `(oneMinus s)` into `(1 - s)` everywhere
  -- now FE fires on the RHS occurrence
  rw [completedRiemannZeta_FE (s := s)]
  -- remaining goal is pure ring arithmetic
  ring

end XiPacket
end Targets
end Hyperlocal
