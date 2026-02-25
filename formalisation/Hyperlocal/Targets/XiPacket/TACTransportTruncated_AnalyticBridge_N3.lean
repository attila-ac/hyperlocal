/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_AnalyticBridge_N3.lean

  Snapshot-robust public API: explicit N=3 transport stencil formulas.

  Goal:
  downstream code can `simp` transport-at-(0/1/2 : Fin 3) directly into
  concrete truncated Taylor expressions,
  without touching `Matrix.mulVec` or any reindexing lemmas.

  Depends only on the algebraic expansion lemma from TACTransportTruncated_AnalyticBridge.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_AnalyticBridge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open scoped BigOperators

/-- Convenience: the `N=3` jet vector. -/
abbrev jetVec3 (f : ℂ → ℂ) (z : ℂ) : Fin 3 → ℂ :=
  jetVec 3 f z

/--
Internal helper: the canonical summand form that `simp` naturally produces
from `transport_apply_eq_truncSum`.
-/
private abbrev summand0 (f : ℂ → ℂ) (z δ : ℂ) (x : ℕ) : ℂ :=
  δ ^ x * ((↑(Nat.factorial x) : ℂ)⁻¹ * cderivIter x f z)

private abbrev summand1 (f : ℂ → ℂ) (z δ : ℂ) (x : ℕ) : ℂ :=
  δ ^ x * ((↑(Nat.factorial x) : ℂ)⁻¹ * cderivIter (x + 1) f z)

/--
Public stencil formula at `j = 0`:

`transport 3 δ Γ 0 = f(z) + f'(z) δ + f''(z) δ^2 / 2`.
-/
@[simp] theorem transport3_apply_fin0
    (f : ℂ → ℂ) (z δ : ℂ) :
    transport 3 δ (jetVec3 f z) (0 : Fin 3)
      =
    (cderivIter 0 f z)
      + (cderivIter 1 f z) * δ
      + (cderivIter 2 f z) * (δ ^ 2) / (2 : ℂ) := by
  classical

  have h :=
    (transport_apply_eq_truncSum (N := 3) (f := f) (z := z) (δ := δ) (j := (0 : Fin 3)))

  -- Put the RHS into the canonical `δ^x * ((x!)⁻¹ * ...)` form that your snapshot simplifies to.
  have hcanon :
      transport 3 δ (jetVec3 f z) (0 : Fin 3)
        =
      (Finset.range 3).sum (fun x => summand0 f z δ x) := by
    -- `j=0` makes `cderivIter ((j:ℕ)+x) = cderivIter x`.
    -- `a / (n! : ℂ)` simp-normalizes to `(↑(n!):ℂ)⁻¹ * a` in your build.
    simpa [jetVec3, summand0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_comm,
      add_left_comm, add_assoc] using h

  -- Now expand `range 3` = {0,1,2}.
  -- `simp` also knows `Nat.factorial 0/1/2` and `δ^0/δ^1/δ^2`.
  -- We finish by rewriting the `((2 : ℂ)⁻¹)` back into `/ (2 : ℂ)`.
  calc
    transport 3 δ (jetVec3 f z) (0 : Fin 3)
        = (Finset.range 3).sum (fun x => summand0 f z δ x) := hcanon
    _ =
        (cderivIter 0 f z)
          + (cderivIter 1 f z) * δ
          + (cderivIter 2 f z) * (δ ^ 2) / (2 : ℂ) := by
        -- Expand sum over range 3; normalize factorials and powers; normalize inverses.
        -- `simp` produces a slightly different multiplication association/order, but it's definitional equal in commutative semiring ℂ.
        simp [summand0, Finset.sum_range_succ, Nat.factorial, pow_two, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]

/--
Public stencil formula at `j = 1`:

`transport 3 δ Γ 1 = f'(z) + f''(z) δ`.
-/
@[simp] theorem transport3_apply_fin1
    (f : ℂ → ℂ) (z δ : ℂ) :
    transport 3 δ (jetVec3 f z) (1 : Fin 3)
      =
    (cderivIter 1 f z)
      + (cderivIter 2 f z) * δ := by
  classical

  have h :=
    (transport_apply_eq_truncSum (N := 3) (f := f) (z := z) (δ := δ) (j := (1 : Fin 3)))

  have hcanon :
      transport 3 δ (jetVec3 f z) (1 : Fin 3)
        =
      (Finset.range 2).sum (fun x => summand1 f z δ x) := by
    -- Here `N - j = 3 - 1 = 2`, and `((j:ℕ)+x) = x+1`.
    simpa [jetVec3, summand1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc] using h

  calc
    transport 3 δ (jetVec3 f z) (1 : Fin 3)
        = (Finset.range 2).sum (fun x => summand1 f z δ x) := hcanon
    _ = (cderivIter 1 f z) + (cderivIter 2 f z) * δ := by
        -- Expand range 2 = {0,1}
        simp [summand1, Finset.sum_range_succ, Nat.factorial, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]

/--
Public stencil formula at `j = 2`:

`transport 3 δ Γ 2 = f''(z)`.
-/
@[simp] theorem transport3_apply_fin2
    (f : ℂ → ℂ) (z δ : ℂ) :
    transport 3 δ (jetVec3 f z) (2 : Fin 3)
      =
    (cderivIter 2 f z) := by
  classical

  have h :=
    (transport_apply_eq_truncSum (N := 3) (f := f) (z := z) (δ := δ) (j := (2 : Fin 3)))

  -- `N - j = 1`, so it’s a singleton sum at x=0.
  -- We don’t even need a separate `summand` helper here.
  have hcanon :
      transport 3 δ (jetVec3 f z) (2 : Fin 3)
        =
      (Finset.range 1).sum (fun x =>
        δ ^ x * ((↑(Nat.factorial x) : ℂ)⁻¹ * cderivIter (x + 2) f z)) := by
    simpa [jetVec3, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc] using h

  calc
    transport 3 δ (jetVec3 f z) (2 : Fin 3)
        = (Finset.range 1).sum (fun x =>
            δ ^ x * ((↑(Nat.factorial x) : ℂ)⁻¹ * cderivIter (x + 2) f z)) := hcanon
    _ = cderivIter 2 f z := by
        -- Expand range 1 = {0}
        simp [Finset.sum_range_succ, Nat.factorial, mul_assoc, mul_left_comm, mul_comm]

end TAC
end XiPacket
end Targets
end Hyperlocal
