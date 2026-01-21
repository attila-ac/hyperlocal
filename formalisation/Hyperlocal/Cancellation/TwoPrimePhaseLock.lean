/-
  Hyperlocal/Cancellation/TwoPrimePhaseLock.lean

  Wrapper: from the extraction lemma + a single arithmetic hypothesis,
  derive the full phase-lock statement used by PrimeWitness.

  This lets PrimeWitness.lean stop carrying the axiom.
-/

import Hyperlocal.Cancellation.TwoPrimePhaseLockCore
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/-- “Not rational” predicate in explicit integer-ratio form. -/
def NotRat (x : ℝ) : Prop :=
  ¬ ∃ m n : ℤ, n ≠ 0 ∧ x = (m : ℝ) / (n : ℝ)

/-
Arithmetic hypothesis (for now):
  log 2 / log 3 is not rational.
Later we can prove this via UFD (2^n = 3^m contradiction) and delete the axiom.
-/
axiom log2_log3_notRat : NotRat (Real.log (2 : ℝ) / Real.log (3 : ℝ))

/--
Phase lock (final interface):
  sin(t log 2)=0 ∧ sin(t log 3)=0 → t=0
discharged up to the single NotRat lemma.
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
        -- divide hm, hn by t
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

        -- ratio cancels (pi/t)
        calc
          Real.log (2 : ℝ) / Real.log (3 : ℝ)
              = ((((m : ℝ) * Real.pi) / t) / (((n : ℝ) * Real.pi) / t)) := by
                  simp [hm', hn']
          _ = (m : ℝ) / (n : ℝ) := by
                  field_simp [Real.pi_ne_zero, ht0, hn_neR]
                  ring

      -- Contradict NotRat
      exact log2_log3_notRat ⟨m, n, hn0, hrat⟩

end PrimeWitness
end Cancellation
end Hyperlocal
