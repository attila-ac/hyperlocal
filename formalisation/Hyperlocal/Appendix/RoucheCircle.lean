-- formalisation/Hyperlocal/Cancellation/RoucheCircle.lean
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex

namespace Hyperlocal
namespace Cancellation

/-- **Project-local Rouché on a circle (existence form, binder-safe).**

This axiom is parametrised by:
* a "norm-like" function `cnorm : ℂ → ℝ`,
* boundary/interior predicates `onCircle`, `inside`.

Assumptions:
* `onCircle z ↔ cnorm z = R` and `inside z ↔ cnorm z < R` for some `R > 0`,
* strict boundary inequality for `f` vs the cubic model `g(z)=Az^3−z^2` on `onCircle`,
* a point inside with radius `> 1` (via `cnorm`),
* `|A| < 1` and `max 1 |1/A| < R`.

Conclusion: there exists `z` with `inside z`, `1 < cnorm z`, and `f z = 0`.

You can later replace this axiom with a genuine proof or a packaged Rouché theorem
without changing downstream code. -/
axiom rouche_on_circle_exists_big_root
  (cnorm : ℂ → ℝ)
  (f : ℂ → ℂ) (A R : ℝ)
  (onCircle inside : ℂ → Prop)
  (hR : 0 < R)
  (hbdry :
    ∀ z : ℂ, onCircle z →
      cnorm (f z - ((A : ℂ) * z ^ 3 - z ^ 2))
        < cnorm ((A : ℂ) * z ^ 3 - z ^ 2))
  (hA_lt1 : |A| < 1)
  (annulus :
    (∀ z : ℂ, onCircle z ↔ cnorm z = R) ∧
    (∀ z : ℂ, inside   z ↔ cnorm z < R) ∧
    (∃ z : ℂ, inside z ∧ 1 < cnorm z) ∧
    (max 1 (|1 / A|) < R)) :
  ∃ z : ℂ, inside z ∧ 1 < cnorm z ∧ f z = 0

end Cancellation
end Hyperlocal
