/-
  Hyperlocal/Targets/XiPacket/TACPrimeWitness_W1.lean

  Unconditional backbone (W1):
  For a linear map F, if F is not identically zero on the span of {c p},
  then there exists p with F (c p) ≠ 0.

  No trig/log/arithmetic needed.
-/

import Mathlib

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

variable {R : Type} [Semiring R]
variable {V : Type} [AddCommMonoid V] [Module R V]
variable {W : Type} [AddCommMonoid W] [Module R W]

/-- W1 kernel lemma: if a linear map vanishes on a set of generators,
then it vanishes on their span. -/
lemma LinearMap.eq_zero_on_span_of_eq_zero_on_set
    (F : V →ₗ[R] W) (S : Set V)
    (hS : ∀ x ∈ S, F x = 0) :
    ∀ y ∈ Submodule.span R S, F y = 0 := by
  intro y hy
  -- In this snapshot, the predicate is `p y (hy : y ∈ span ...)`.
  refine
    Submodule.span_induction
      (p := fun y _hy => F y = 0)
      (fun x hx => hS x hx)
      (by simpa using (map_zero F))
      (fun x y hx hy hxF hyF => by simpa [map_add, hxF, hyF])
      (fun a x hx hxF => by simpa [map_smul, hxF])
      hy

/-- W1 existence form: if F is not identically zero on the span of {c p},
then some generator escapes the kernel. -/
lemma exists_generator_not_in_kernel_of_not_eq_zero_on_span
    (F : V →ₗ[R] W) (c : ℕ → V) :
    (∃ y ∈ Submodule.span R (Set.range c), F y ≠ 0) →
    (∃ n : ℕ, F (c n) ≠ 0) := by
  intro h_nonzero
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ n, F (c n) = 0
  have h_on_set : ∀ x ∈ (Set.range c), F x = 0 := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact h_all n
  have h_on_span :
      ∀ y ∈ Submodule.span R (Set.range c), F y = 0 :=
    LinearMap.eq_zero_on_span_of_eq_zero_on_set (F := F) (S := Set.range c) h_on_set
  rcases h_nonzero with ⟨y, hy, hFy⟩
  exact hFy (h_on_span y hy)

end TAC
end XiPacket
end Targets
end Hyperlocal
