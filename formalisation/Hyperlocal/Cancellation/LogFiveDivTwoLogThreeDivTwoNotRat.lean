/-
  Hyperlocal/Cancellation/LogFiveDivTwoLogThreeDivTwoNotRat.lean

  Arithmetic discharge for the second finite witness pair {2,5} against the
  exact resonance branch for {2,3}.

  Main output:
    NotRat ( log(5/2) / log(3/2) ).

  This is the precise arithmetic fact needed to show that an exact resonance at
  log(3/2) cannot simultaneously be an exact resonance at log(5/2) when t ≠ 0.

  Strategy:
    log(5/2) / log(3/2) = m/n
      ⇒ (5/2)^N = (3/2)^M
      ⇒ 5^N * 2^M = 3^M * 2^N
      ⇒ 5 divides RHS
      ⇒ 5 divides 3^M or 2^N
      ⇒ contradiction.
-/

import Hyperlocal.Cancellation.Log2Log3NotRat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/--
If `log(5/2) / log(3/2)` is rational, then after clearing signs one obtains
natural exponents `M,N` with `N ≠ 0` and
  5^N * 2^M = 3^M * 2^N.
-/
lemma log52_log32_rat_imp_cross_pow_eq
    {m n : ℤ} (hn0 : n ≠ 0)
    (h :
      Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ))
        =
      (m : ℝ) / (n : ℝ)) :
    ∃ M N : ℕ, N ≠ 0 ∧
      (5 : ℕ) ^ N * (2 : ℕ) ^ M = (3 : ℕ) ^ M * (2 : ℕ) ^ N := by
  have h52pos : (0 : ℝ) < ((5 : ℝ) / (2 : ℝ)) := by norm_num
  have h32pos : (0 : ℝ) < ((3 : ℝ) / (2 : ℝ)) := by norm_num

  have hlog52pos : (0 : ℝ) < Real.log ((5 : ℝ) / (2 : ℝ)) := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < ((5 : ℝ) / (2 : ℝ)))
  have hlog32pos : (0 : ℝ) < Real.log ((3 : ℝ) / (2 : ℝ)) := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < ((3 : ℝ) / (2 : ℝ)))

  have hmul :
      (n : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ))
        =
      (m : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hlog32ne : Real.log ((3 : ℝ) / (2 : ℝ)) ≠ 0 := ne_of_gt hlog32pos
    have h' := congrArg
      (fun x => x * ((n : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)))) h
    have :
        (Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ)))
            * ((n : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)))
          =
        ((m : ℝ) / (n : ℝ))
            * ((n : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ))) := by
      simpa using h'
    calc
      (n : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ))
          =
        (Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ)))
          * ((n : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ))) := by
            field_simp [hlog32ne]
            ring
      _ =
        ((m : ℝ) / (n : ℝ))
          * ((n : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ))) := by
            simpa using this
      _ = (m : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
            field_simp [hnR]
            ring

  have hn_cases : (0 : ℤ) ≤ n ∨ n < 0 := le_or_gt 0 n
  cases hn_cases with
  | inl hn_nonneg =>
      have hn_posZ : (0 : ℤ) < n := lt_of_le_of_ne hn_nonneg (Ne.symm hn0)
      have hn_posR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_posZ

      have hLpos :
          (0 : ℝ) < (n : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ)) := by
        exact mul_pos hn_posR hlog52pos
      have hRpos :
          (0 : ℝ) < (m : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
        simpa [hmul] using hLpos

      have hm_posR : (0 : ℝ) < (m : ℝ) := by
        have htmp :
            ((0 : ℝ) < (m : ℝ) ∧
              (0 : ℝ) < Real.log ((3 : ℝ) / (2 : ℝ)))
              ∨
            ((m : ℝ) < 0 ∧
              Real.log ((3 : ℝ) / (2 : ℝ)) < 0) := by
          simpa [mul_pos_iff] using hRpos
        cases htmp with
        | inl hp => exact hp.1
        | inr hn' => exact False.elim (lt_asymm hn'.2 hlog32pos)

      have hm_nonneg : (0 : ℤ) ≤ m := by
        exact_mod_cast (le_of_lt hm_posR)

      let N : ℕ := Int.toNat n
      let M : ℕ := Int.toNat m

      have hn_castZ : (N : ℤ) = n := by
        simp [N, Int.toNat_of_nonneg hn_nonneg]
      have hm_castZ : (M : ℤ) = m := by
        simp [M, Int.toNat_of_nonneg hm_nonneg]

      have hN0 : N ≠ 0 := by
        intro hN
        have : n = 0 := by
          have : (N : ℤ) = 0 := by simpa [hN]
          simpa [hn_castZ] using this
        exact hn0 this

      have hn_castR : (N : ℝ) = (n : ℝ) := by exact_mod_cast hn_castZ
      have hm_castR : (M : ℝ) = (m : ℝ) := by exact_mod_cast hm_castZ

      have hmulNM :
          (N : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ))
            =
          (M : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
        simpa [hn_castR, hm_castR] using hmul

      have hexpNM :
          Real.exp ((N : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ)))
            =
          Real.exp ((M : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ))) := by
        simpa using congrArg Real.exp hmulNM

      have hpowR :
          (((5 : ℝ) / (2 : ℝ)) ^ N)
            =
          (((3 : ℝ) / (2 : ℝ)) ^ M) := by
        simpa [exp_nat_mul_log (a := ((5 : ℝ) / (2 : ℝ))) h52pos,
               exp_nat_mul_log (a := ((3 : ℝ) / (2 : ℝ))) h32pos] using hexpNM

      have hpowR' := hpowR
      rw [div_pow, div_pow] at hpowR'
      have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
      have h2M : (2 : ℝ) ^ M ≠ 0 := by positivity

      have h1 :
          (5 : ℝ) ^ N =
            (((3 : ℝ) ^ M) / ((2 : ℝ) ^ M)) * ((2 : ℝ) ^ N) := by
        exact (div_eq_iff h2N).mp hpowR'

      have h2eq :=
        congrArg (fun x : ℝ => x * ((2 : ℝ) ^ M)) h1

      have hcross :
          (5 : ℝ) ^ N * (2 : ℝ) ^ M
            =
          (3 : ℝ) ^ M * (2 : ℝ) ^ N := by
        calc
          (5 : ℝ) ^ N * (2 : ℝ) ^ M
              =
            ((((3 : ℝ) ^ M) / ((2 : ℝ) ^ M)) * ((2 : ℝ) ^ N)) * ((2 : ℝ) ^ M) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using h2eq
          _ = (3 : ℝ) ^ M * (2 : ℝ) ^ N := by
                field_simp [h2M]

      have hpowN :
          (5 : ℕ) ^ N * (2 : ℕ) ^ M = (3 : ℕ) ^ M * (2 : ℕ) ^ N := by
        exact_mod_cast hcross

      exact ⟨M, N, hN0, hpowN⟩

  | inr hn_neg =>
      have hn_negR : (n : ℝ) < 0 := by exact_mod_cast hn_neg
      have hLneg :
          (n : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ)) < 0 := by
        exact mul_neg_of_neg_of_pos hn_negR hlog52pos
      have hRneg :
          (m : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) < 0 := by
        simpa [hmul] using hLneg

      have hm_negR : (m : ℝ) < 0 := by
        have htmp :
            (0 < (m : ℝ) ∧ Real.log ((3 : ℝ) / (2 : ℝ)) < 0)
              ∨
            ((m : ℝ) < 0 ∧ 0 < Real.log ((3 : ℝ) / (2 : ℝ))) := by
          simpa [mul_neg_iff] using hRneg
        have htmp' :
            ((m : ℝ) < 0 ∧ 0 < Real.log ((3 : ℝ) / (2 : ℝ)))
              ∨
            (0 < (m : ℝ) ∧ Real.log ((3 : ℝ) / (2 : ℝ)) < 0) :=
          Or.comm.mp htmp
        cases htmp' with
        | inl hmn => exact hmn.1
        | inr hp  => exact False.elim (lt_asymm hp.2 hlog32pos)

      have hm_negZ : m < 0 := by exact_mod_cast hm_negR

      have hn'_nonneg : (0 : ℤ) ≤ (-n) := le_of_lt (neg_pos.mpr hn_neg)
      have hm'_nonneg : (0 : ℤ) ≤ (-m) := le_of_lt (neg_pos.mpr hm_negZ)

      let N : ℕ := Int.toNat (-n)
      let M : ℕ := Int.toNat (-m)

      have hn_castZ : (N : ℤ) = (-n) := by
        simp [N, Int.toNat_of_nonneg hn'_nonneg]
      have hm_castZ : (M : ℤ) = (-m) := by
        simp [M, Int.toNat_of_nonneg hm'_nonneg]

      have hN0 : N ≠ 0 := by
        intro hN
        have : (-n) = 0 := by
          have : (N : ℤ) = 0 := by simpa [hN]
          simpa [hn_castZ] using this
        have : n = 0 := by simpa using (neg_eq_zero.mp this)
        exact hn0 this

      have hn_castR : (N : ℝ) = ((-n) : ℝ) := by exact_mod_cast hn_castZ
      have hm_castR : (M : ℝ) = ((-m) : ℝ) := by exact_mod_cast hm_castZ

      have hmul' :
          ((-n) : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ))
            =
          ((-m) : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
        nlinarith [hmul]

      have hmulNM :
          (N : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ))
            =
          (M : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ)) := by
        simpa [hn_castR, hm_castR] using hmul'

      have hexpNM :
          Real.exp ((N : ℝ) * Real.log ((5 : ℝ) / (2 : ℝ)))
            =
          Real.exp ((M : ℝ) * Real.log ((3 : ℝ) / (2 : ℝ))) := by
        simpa using congrArg Real.exp hmulNM

      have hpowR :
          (((5 : ℝ) / (2 : ℝ)) ^ N)
            =
          (((3 : ℝ) / (2 : ℝ)) ^ M) := by
        simpa [exp_nat_mul_log (a := ((5 : ℝ) / (2 : ℝ))) h52pos,
               exp_nat_mul_log (a := ((3 : ℝ) / (2 : ℝ))) h32pos] using hexpNM

      have hpowR' := hpowR
      rw [div_pow, div_pow] at hpowR'
      have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
      have h2M : (2 : ℝ) ^ M ≠ 0 := by positivity

      have h1 :
          (5 : ℝ) ^ N =
            (((3 : ℝ) ^ M) / ((2 : ℝ) ^ M)) * ((2 : ℝ) ^ N) := by
        exact (div_eq_iff h2N).mp hpowR'

      have h2eq :=
        congrArg (fun x : ℝ => x * ((2 : ℝ) ^ M)) h1

      have hcross :
          (5 : ℝ) ^ N * (2 : ℝ) ^ M
            =
          (3 : ℝ) ^ M * (2 : ℝ) ^ N := by
        calc
          (5 : ℝ) ^ N * (2 : ℝ) ^ M
              =
            ((((3 : ℝ) ^ M) / ((2 : ℝ) ^ M)) * ((2 : ℝ) ^ N)) * ((2 : ℝ) ^ M) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using h2eq
          _ = (3 : ℝ) ^ M * (2 : ℝ) ^ N := by
                field_simp [h2M]

      have hpowN :
          (5 : ℕ) ^ N * (2 : ℕ) ^ M = (3 : ℕ) ^ M * (2 : ℕ) ^ N := by
        exact_mod_cast hcross

      exact ⟨M, N, hN0, hpowN⟩

/--
Final arithmetic fact:

  `NotRat (log(5/2) / log(3/2))`.
-/
theorem log52_log32_notRat :
    NotRat (Real.log ((5 : ℝ) / (2 : ℝ)) / Real.log ((3 : ℝ) / (2 : ℝ))) := by
  intro h
  rcases h with ⟨m, n, hn0, hrat⟩
  rcases log52_log32_rat_imp_cross_pow_eq (m := m) (n := n) hn0 hrat with
    ⟨M, N, hN0, hMN⟩

  rcases Nat.exists_eq_succ_of_ne_zero hN0 with ⟨k, hk⟩
  have h5dvdL : (5 : ℕ) ∣ (5 : ℕ) ^ N * (2 : ℕ) ^ M := by
    subst hk
    refine ⟨(5 : ℕ) ^ k * (2 : ℕ) ^ M, ?_⟩
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

  have h5dvdR : (5 : ℕ) ∣ (3 : ℕ) ^ M * (2 : ℕ) ^ N := by
    simpa [hMN] using h5dvdL

  have hp5 : Nat.Prime 5 := by decide
  rcases hp5.dvd_mul.mp h5dvdR with h53 | h52
  · have h5dvd3 : (5 : ℕ) ∣ (3 : ℕ) := hp5.dvd_of_dvd_pow h53
    norm_num at h5dvd3
  · have h5dvd2 : (5 : ℕ) ∣ (2 : ℕ) := hp5.dvd_of_dvd_pow h52
    norm_num at h5dvd2

end PrimeWitness
end Cancellation
end Hyperlocal
