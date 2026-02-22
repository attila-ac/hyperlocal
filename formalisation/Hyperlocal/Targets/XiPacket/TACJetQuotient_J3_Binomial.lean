/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_Binomial.lean

  Binomial truncation engine in J3 := ℂ[w]/(w^3):

    u(δ) := C δ + w

  We prove:
    (u(δ))^n = ∑_{k=0}^{2} (choose n k) * (C δ)^(n-k) * w^k
  because w^k = 0 for k ≥ 3.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_Algebra
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex
open scoped BigOperators

namespace J3

/-- Abbreviation: the shift element u(δ) = C δ + w. -/
abbrev uδ (δ : ℂ) : J3 := u δ

/--
A binomial expansion of `(u δ)^n` in the form we want: coefficients times `(C δ)^(n-k) * w^k`.

We choose the `add_pow` orientation so that the second summand (`C δ`) gets exponent `(n-k)`
and the first summand (`w`) gets exponent `k`.
-/
lemma u_pow_eq_sum_choose (δ : ℂ) (n : ℕ) :
    (uδ δ) ^ n
      =
    (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k) := by
  classical
  -- Use add_pow with arguments (w) (C δ).
  have h := add_pow (w : J3) (C δ) n
  -- h expands (w + Cδ)^n. Our uδ is (Cδ + w), so commute the add on the LHS.
  -- The RHS already has the desired (Cδ)^(n-k) * w^k order in this Mathlib snapshot.
  simpa [uδ, u, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using h

/--
Truncated binomial expansion: only k = 0,1,2 survive because w^k = 0 for k ≥ 3.
-/
lemma u_pow_eq_sum_choose_range_three (δ : ℂ) (n : ℕ) :
    (uδ δ) ^ n
      =
    (Finset.range 3).sum (fun k =>
      (Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k) := by
  classical
  cases n with
  | zero =>
      -- n = 0
      -- LHS = 1
      -- RHS = choose 0 0 * (Cδ)^0 * w^0 + choose 0 1 * ... + choose 0 2 * ...
      -- and choose 0 1 = choose 0 2 = 0.
      simp [Finset.range_succ, Finset.sum_cons, Finset.sum_singleton]
  | succ n =>
      cases n with
      | zero =>
          -- n = 1
          -- LHS = uδ δ = Cδ + w
          -- RHS has only k=0 and k=1 nonzero; k=2 term killed by choose 1 2 = 0.
          -- Also note: (Cδ)^(1-0)=Cδ, (Cδ)^(1-1)=1, w^1=w, w^0=1.
          simp [uδ, u, Finset.range_succ, Finset.sum_cons, Finset.sum_singleton, add_comm, add_left_comm,
            add_assoc, mul_assoc, mul_left_comm, mul_comm]
      | succ n =>
          -- n = succ (succ n) ≥ 2
          let n2 : ℕ := Nat.succ (Nat.succ n)
          have hN : 3 ≤ n2 + 1 := by
            -- n2+1 = n+3, so 3 ≤ n+3
            simpa [n2, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Nat.le_add_left 3 n)
          rw [u_pow_eq_sum_choose (δ := δ) (n := n2)]
          simpa [n2, mul_assoc, mul_left_comm, mul_comm] using
            (sum_range_eq_sum_range_three_of_w_nil
              (a := fun k => (Nat.choose n2 k : J3) * (C δ) ^ (n2 - k))
              (N := n2 + 1) hN)

end J3

end TAC
end XiPacket
end Targets
end Hyperlocal
