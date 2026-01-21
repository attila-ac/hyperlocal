/-
  Hyperlocal/Cancellation/TwoPrimePhaseLock.lean

  Wrapper: from the extraction lemma + discharged arithmetic fact,
  derive the full phase-lock statement used by PrimeWitness.

  No arithmetic axioms remain: we import Log2Log3NotRat.lean.
-/

import Hyperlocal.Cancellation.TwoPrimePhaseLockCore
import Hyperlocal.Cancellation.Log2Log3NotRat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/--
Phase lock (final interface):
  sin(t log 2)=0 ∧ sin(t log 3)=0 → t=0
-/
theorem two_prime_phase_lock (t : ℝ) :
  Real.sin (t * Real.log (2 : ℝ)) = 0 ∧
  Real.sin (t * Real.log (3 : ℝ)) = 0 → t = 0 := by
  intro h
  have hx := two_prime_phase_lock_extract t h
  cases hx with
  | inl ht => exact ht
  | inr hmn =>
      rcases hmn with ⟨m, n, hm, hn, hn_nontriv⟩
      by_contra ht
      have ht0 : t ≠ 0 := ht
      have hn0 : n ≠ 0 := hn_nontriv ht0

      have hrat : Real.log (2 : ℝ) / Real.log (3 : ℝ) = (m : ℝ) / (n : ℝ) := by
        have hm' : Real.log (2 : ℝ) = ((m : ℝ) * Real.pi) / t := by
          have := congrArg (fun x => x / t) hm
          simp [mul_div_cancel_left₀, ht0] at this
          exact this

        have hn' : Real.log (3 : ℝ) = ((n : ℝ) * Real.pi) / t := by
          have := congrArg (fun x => x / t) hn
          simp [mul_div_cancel_left₀, ht0] at this
          exact this

        have hn_neR : (n : ℝ) ≠ 0 := by
          exact Int.cast_ne_zero.mpr hn0

        calc
          Real.log (2 : ℝ) / Real.log (3 : ℝ)
              = ((((m : ℝ) * Real.pi) / t) / (((n : ℝ) * Real.pi) / t)) := by
                  simp [hm', hn']
          _ = (m : ℝ) / (n : ℝ) := by
                  field_simp [Real.pi_ne_zero, ht0, hn_neR]
                  ring

      -- Contradict the proved NotRat lemma (from Log2Log3NotRat.lean)
      exact log2_log3_notRat ⟨m, n, hn0, hrat⟩

end PrimeWitness
end Cancellation
end Hyperlocal
