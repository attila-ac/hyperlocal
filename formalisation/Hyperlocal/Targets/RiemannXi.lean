/-
  Hyperlocal/Targets/RiemannXi.lean

  Target function for the Stage-3 instantiation.

  We take ξ to be Mathlib's "entire completed Riemann zeta with poles removed",
  namely `completedRiemannZeta₀`.

  This file is intentionally lightweight: it only pins down the target `ξ : ℂ → ℂ`
  as an actual Lean constant/definition.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

namespace Hyperlocal
namespace Targets

/-- The Riemann ξ-function used as the target in the hyperlocal development. -/
abbrev xi : ℂ → ℂ := completedRiemannZeta₀

end Targets

/-- Convenience re-export: `Hyperlocal.xi` is the target ξ-function. -/
abbrev xi : ℂ → ℂ := Targets.xi

/-- Notation for the target Riemann ξ-function. -/
notation "ξ" => Hyperlocal.xi

end Hyperlocal
