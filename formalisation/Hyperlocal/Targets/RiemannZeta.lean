/-
  Hyperlocal/Targets/RiemannZeta.lean

  Canonical target: the Riemann ζ-function from Mathlib.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

namespace Hyperlocal

/-- Canonical ζ target (Mathlib’s `riemannZeta`). -/
abbrev zeta : ℂ → ℂ := riemannZeta

end Hyperlocal
