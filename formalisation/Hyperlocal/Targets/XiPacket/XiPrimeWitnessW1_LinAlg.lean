/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_LinAlg.lean

  Way 1 (W1) backbone: purely linear-algebra facts.

  Core deterministic lemma:
    if a linear map vanishes on all generators of a span, it vanishes on the span.
  Hence if it does *not* vanish on the span, at least one generator has nonzero image.

  Snapshot note (Lean 4.23 rc2 / your Mathlib):
  `Mathlib.LinearAlgebra.Basic` is not present, so we import the minimal
  linear-map core used elsewhere in this repo:
    `Mathlib.Algebra.Module.LinearMap.Basic`.
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

section

variable {R V W ι : Type}
variable [Semiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- If `F` kills every generator in `range v`, then it kills the `span` of those generators. -/
theorem map_eq_zero_on_span_of_eq_zero_on_generators
    (F : V →ₗ[R] W) (v : ι → V)
    (hv : ∀ i : ι, F (v i) = 0) :
    ∀ x : V, x ∈ Submodule.span R (Set.range v) → F x = 0 := by
  intro x hx
  -- Show: `span (range v)` is contained in `ker F`.
  have hle : Submodule.span R (Set.range v) ≤ LinearMap.ker F := by
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    -- `v i ∈ ker F` because `F (v i) = 0`.
    simpa [LinearMap.mem_ker] using hv i
  have hxker : x ∈ LinearMap.ker F := hle hx
  simpa [LinearMap.mem_ker] using hxker

/-- Contrapositive form: if `F` is nonzero on the span, then some generator is nonzero. -/
theorem exists_generator_of_exists_span_ne_zero
    (F : V →ₗ[R] W) (v : ι → V)
    (hspan : ∃ x : V, x ∈ Submodule.span R (Set.range v) ∧ F x ≠ 0) :
    ∃ i : ι, F (v i) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  rcases hspan with ⟨x, hxspan, hxne⟩
  have hx0 : F x = 0 :=
    map_eq_zero_on_span_of_eq_zero_on_generators (F := F) (v := v) h x hxspan
  exact hxne hx0

end

end W1
end XiPacket
end Targets
end Hyperlocal
