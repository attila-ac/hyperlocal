/-
  Hyperlocal/Cancellation/TwoPrimePhaseLockCore.lean

  Core reduction (stable on Lean 4.23.0-rc2 snapshot):

  If sin(t log 2)=0 and sin(t log 3)=0 then either t=0
  or there exist integers m,n such that
    t*log 2 = m*pi and t*log 3 = n*pi
  with n ≠ 0 (so the second relation is nontrivial when t ≠ 0).

  This is the “bookkeeping” part that is independent of UFD/parity.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/-- `sin x = 0` ⇒ ∃ k : ℤ, x = (k:ℝ)*π. (Mathlib returns the reverse equality.) -/
lemma sin_eq_int_mul_pi {x : ℝ} (hx : Real.sin x = 0) :
    ∃ k : ℤ, x = (k : ℝ) * Real.pi := by
  rcases (Real.sin_eq_zero_iff.mp hx) with ⟨k, hk⟩
  exact ⟨k, hk.symm⟩

/--
Core extraction lemma:
Two sine vanishings force integer π-multiple identities.
-/
theorem two_prime_phase_lock_extract (t : ℝ) :
    (Real.sin (t * Real.log (2 : ℝ)) = 0 ∧ Real.sin (t * Real.log (3 : ℝ)) = 0) →
    (t = 0 ∨
      ∃ m n : ℤ,
        (t * Real.log (2 : ℝ) = (m : ℝ) * Real.pi) ∧
        (t * Real.log (3 : ℝ) = (n : ℝ) * Real.pi) ∧
        (t ≠ 0 → n ≠ 0)) := by
  intro h
  by_cases ht : t = 0
  · exact Or.inl ht
  · right
    have ht0 : t ≠ 0 := ht
    rcases sin_eq_int_mul_pi (x := t * Real.log (2 : ℝ)) h.1 with ⟨m, hm⟩
    rcases sin_eq_int_mul_pi (x := t * Real.log (3 : ℝ)) h.2 with ⟨n, hn⟩
    refine ⟨m, n, ?_, ?_, ?_⟩
    · simp [hm]
    · simp [hn]
    · intro _ht
      -- If n=0, then t*log 3 = 0, hence log 3 = 0 (since t≠0),
      -- but exp(log 3)=3 for 3>0, so contradiction.
      intro hn0
      have htn : t * Real.log (3 : ℝ) = 0 := by
        -- from hn : t*log3 = (n:ℝ)*π, and n=0
        simp [hn, hn0]
      have hlog3 : Real.log (3 : ℝ) = 0 := by
        have := congrArg (fun x => x / t) htn
        simpa [mul_div_cancel_left₀, ht0] using this
      have hpos : (0 : ℝ) < (3 : ℝ) := by norm_num
      have h3eq1 : (3 : ℝ) = 1 := by
        have := congrArg Real.exp hlog3
        -- exp(log 3)=3, exp(0)=1
        simpa [Real.exp_log hpos] using this
      norm_num at h3eq1

end PrimeWitness
end Cancellation
end Hyperlocal
