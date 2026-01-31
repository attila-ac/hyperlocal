/-
  Hyperlocal/Targets/RiemannXi.lean

  Target definition of the Riemann ξ-function used by the v4.0/v4.1 track.

  We use the classical multiplicative completion (up to the standard nonzero
  scalar factors already inside `completedRiemannZeta`):

      ξ(s) := s * (s - 1) * completedRiemannZeta s.

  This shares the same nontrivial zeros as ζ (away from the real axis).
-/

import Hyperlocal.Targets.RiemannZeta
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal

/-- Riemann ξ-function target: `s * (s - 1) * completedRiemannZeta s`. -/
abbrev xi : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta s

end Hyperlocal
