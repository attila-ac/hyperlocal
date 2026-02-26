/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1.lean

  Way 1 (W1) prime-witness backbone, packaged as a minimal gate.

  Snapshot note (Lean 4.23 rc2 / your Mathlib):
  `Mathlib.LinearAlgebra.Basic` is not present, so we import the minimal
  linear-map core `Mathlib.Algebra.Module.LinearMap.Basic`.

  IMPORTANT Lean note:
  This gate carries *data* (`c`, `F`) as well as a proof (`nontrivial`), so it
  must be `: Type` (not `: Prop`), otherwise projections are forbidden.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_LinAlg
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

section

variable {R V W : Type}
variable [Semiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

variable {H : ℂ → ℂ}

/-- Prime index type used for W1: the subtype of natural primes. -/
abbrev PrimeIdx : Type := {p : ℕ // Nat.Prime p}

/--
W1 gate: for an off-critical seed `s`, provide
  * a family of prime-window generators `c p : V`,
  * a Stage-2 linear map `F : V →ₗ[R] W`,
  * and the nontriviality claim: if `t ≠ 0` (which holds for `OffSeed`), then
    `F` is not identically zero on the span of those generators.

This is a `Type`-class because it carries data fields (`c`, `F`).
-/
class XiPrimeWitnessW1 (s : Hyperlocal.OffSeed H) : Type where
  /-- Generator family indexed by primes. -/
  c : PrimeIdx → V
  /-- Stage-2 linear map (finite-dimensional pipeline). -/
  F : V →ₗ[R] W
  /-- Nontriviality on the prime span (the analytic cliff). -/
  nontrivial (ht : s.ρ.im ≠ 0) :
    ∃ x : V, x ∈ Submodule.span R (Set.range c) ∧ F x ≠ 0

/--
Deterministic consequence of the W1 gate:
there exists a prime `p` whose generator has nonzero image under `F`.
-/
theorem exists_prime_witness
    {s : Hyperlocal.OffSeed H} [XiPrimeWitnessW1 (R := R) (V := V) (W := W) s]
    (ht : s.ρ.im ≠ 0) :
    ∃ p : PrimeIdx,
      (XiPrimeWitnessW1.F (s := s) (R := R) (V := V) (W := W))
        ((XiPrimeWitnessW1.c (s := s) (R := R) (V := V) (W := W)) p) ≠ 0 := by
  classical
  rcases (XiPrimeWitnessW1.nontrivial (s := s) (R := R) (V := V) (W := W) ht) with
    ⟨x, hxspan, hxne⟩
  simpa using
    (exists_generator_of_exists_span_ne_zero
      (F := XiPrimeWitnessW1.F (s := s) (R := R) (V := V) (W := W))
      (v := XiPrimeWitnessW1.c (s := s) (R := R) (V := V) (W := W))
      (hspan := ⟨x, hxspan, hxne⟩))

end

end W1
end XiPacket
end Targets
end Hyperlocal
