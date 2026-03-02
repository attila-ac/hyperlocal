/-
  Hyperlocal/Targets/RiemannXi.lean
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

open Complex

/--
Riemann xi-function used by the Hyperlocal development.

IMPORTANT:
We use the **entire extension** of the pole-cancelled product:
  xi(s) := s (s - 1) Λ₀(s) + 1.

This agrees with the raw product `s(s-1)Λ(s)` on `s ≠ 0, 1`,
but unlike the raw product it is analytic at `0` and `1` in Lean
(avoids the `inv 0 = 0` definitional pathology).
-/
abbrev xi : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1

end Hyperlocal
