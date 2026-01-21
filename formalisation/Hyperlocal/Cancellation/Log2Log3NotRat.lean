/-
  Hyperlocal/Cancellation/Log2Log3NotRat.lean

  Discharge the last arithmetic bottleneck:

    NotRat (log 2 / log 3)

  Strategy (robust, no fragile lemma names like Real.exp_int_mul_log, no parity modules):
    log2/log3 = m/n  (m,n:ℤ, n≠0)
    ⇒ (n:ℝ)*log2 = (m:ℝ)*log3
    ⇒ using positivity of log2,log3: n and m have the same sign
    ⇒ reduce to naturals N=|n|, M=|m| with (N:ℝ)*log2 = (M:ℝ)*log3
    ⇒ exp: 2^N = 3^M  (as ℝ, then as ℕ)
    ⇒ since N≠0, 2 ∣ 2^N, hence 2 ∣ 3^M, but (3^M) % 2 = 1. Contradiction.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

/-- “Not rational” predicate in explicit integer-ratio form. -/
def NotRat (x : ℝ) : Prop :=
  ¬ ∃ m n : ℤ, n ≠ 0 ∧ x = (m : ℝ) / (n : ℝ)

/-- Helper: for `a>0` and `k:ℕ`, `exp((k:ℝ) * log a) = a^k`. -/
lemma exp_nat_mul_log (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.exp ((k : ℝ) * Real.log a) = a ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        Real.exp (((Nat.succ k : ℕ) : ℝ) * Real.log a)
            = Real.exp (((k : ℝ) + 1) * Real.log a) := by
                simp [Nat.cast_add, Nat.cast_one]
        _ = Real.exp ((k : ℝ) * Real.log a + 1 * Real.log a) := by
                ring_nf
        _ = Real.exp ((k : ℝ) * Real.log a) * Real.exp (1 * Real.log a) := by
                simp [Real.exp_add]
        _ = (a ^ k) * a := by
                simp [ih, Real.exp_log ha]
        _ = a ^ (Nat.succ k) := by
                simp [pow_succ, mul_assoc]

/-- Helper: `(3^M) % 2 = 1` for all naturals `M`. -/
lemma pow3_mod2 (M : ℕ) : (3 ^ M) % 2 = 1 := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      -- (3^(M+1)) % 2 = ((3^M)*3) % 2 = ((3^M)%2*(3%2))%2 = (1*1)%2 = 1
      simp [pow_succ, Nat.mul_mod, ih]

/--
Main reduction:
if `log2/log3 = m/n` with integers (n≠0), we get naturals M,N with N≠0 and `2^N = 3^M`.
-/
lemma log2_log3_rat_imp_pow_eq
    {m n : ℤ} (hn0 : n ≠ 0)
    (h : Real.log (2 : ℝ) / Real.log (3 : ℝ) = (m : ℝ) / (n : ℝ)) :
    ∃ M N : ℕ, N ≠ 0 ∧ (2 : ℕ) ^ N = (3 : ℕ) ^ M := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have h3pos : (0 : ℝ) < (3 : ℝ) := by norm_num
  have hlog2pos : (0 : ℝ) < Real.log (2 : ℝ) := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℝ))
  have hlog3pos : (0 : ℝ) < Real.log (3 : ℝ) := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < (3 : ℝ))

  -- Clear denominators: (n:ℝ)*log2 = (m:ℝ)*log3
  have hmul : (n : ℝ) * Real.log (2 : ℝ) = (m : ℝ) * Real.log (3 : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hlog3ne : Real.log (3 : ℝ) ≠ 0 := ne_of_gt hlog3pos
    have h' := congrArg (fun x => x * ((n : ℝ) * Real.log (3 : ℝ))) h
    have : (Real.log (2 : ℝ) / Real.log (3 : ℝ)) * ((n : ℝ) * Real.log (3 : ℝ))
          = ((m : ℝ) / (n : ℝ)) * ((n : ℝ) * Real.log (3 : ℝ)) := by
      simpa using h'
    calc
      (n : ℝ) * Real.log (2 : ℝ)
          = (Real.log (2 : ℝ) / Real.log (3 : ℝ)) * ((n : ℝ) * Real.log (3 : ℝ)) := by
              field_simp [hlog3ne]
              ring
      _ = ((m : ℝ) / (n : ℝ)) * ((n : ℝ) * Real.log (3 : ℝ)) := by
              simpa using this
      _ = (m : ℝ) * Real.log (3 : ℝ) := by
              field_simp [hnR]
              ring

  -- Split on sign of n
  have hn_cases : (0 : ℤ) ≤ n ∨ n < 0 := le_or_gt 0 n
  cases hn_cases with
  | inl hn_nonneg =>
      -- n > 0 since n≠0
      have hn_posZ : (0 : ℤ) < n := lt_of_le_of_ne hn_nonneg (Ne.symm hn0)
      have hn_posR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_posZ

      -- LHS positive ⇒ RHS positive ⇒ m positive
      have hLpos : (0 : ℝ) < (n : ℝ) * Real.log (2 : ℝ) := mul_pos hn_posR hlog2pos
      have hRpos : (0 : ℝ) < (m : ℝ) * Real.log (3 : ℝ) := by simpa [hmul] using hLpos

      have hm_posR : (0 : ℝ) < (m : ℝ) := by
        have htmp : ((0 : ℝ) < (m : ℝ) ∧ (0 : ℝ) < Real.log (3 : ℝ)) ∨
                    ((m : ℝ) < 0 ∧ Real.log (3 : ℝ) < 0) := by
          simpa [mul_pos_iff] using hRpos
        cases htmp with
        | inl hp => exact hp.1
        | inr hn' => exact False.elim (lt_asymm hn'.2 hlog3pos)

      have hm_nonneg : (0 : ℤ) ≤ m := by exact_mod_cast (le_of_lt hm_posR)

      let N : ℕ := Int.toNat n
      let M : ℕ := Int.toNat m

      have hn_castZ : (N : ℤ) = n := by
        simp [N, Int.toNat_of_nonneg hn_nonneg]
      have hm_castZ : (M : ℤ) = m := by
        simp [M, Int.toNat_of_nonneg hm_nonneg]

      have hN0 : N ≠ 0 := by
        intro hN
        have : n = 0 := by
          -- from (N:ℤ)=n and N=0
          have : (N : ℤ) = 0 := by simpa [hN]
          exact (by simpa [hn_castZ] using this)
        exact hn0 this

      have hn_castR : (N : ℝ) = (n : ℝ) := by exact_mod_cast hn_castZ
      have hm_castR : (M : ℝ) = (m : ℝ) := by exact_mod_cast hm_castZ

      have hmulNM : (N : ℝ) * Real.log (2 : ℝ) = (M : ℝ) * Real.log (3 : ℝ) := by
        simpa [hn_castR, hm_castR] using hmul

      have hexpNM :
          Real.exp ((N : ℝ) * Real.log (2 : ℝ)) =
          Real.exp ((M : ℝ) * Real.log (3 : ℝ)) := by
        simpa using congrArg Real.exp hmulNM

      have hpowR : (2 : ℝ) ^ N = (3 : ℝ) ^ M := by
        simpa [exp_nat_mul_log (a := (2 : ℝ)) h2pos,
               exp_nat_mul_log (a := (3 : ℝ)) h3pos] using hexpNM

      have hpowN : (2 : ℕ) ^ N = (3 : ℕ) ^ M := by
        have hcast : ((2 : ℕ) ^ N : ℝ) = ((3 : ℕ) ^ M : ℝ) := by
          simpa [Nat.cast_pow, Nat.cast_ofNat] using hpowR
        exact_mod_cast hcast

      exact ⟨M, N, hN0, hpowN⟩

  | inr hn_neg =>
      -- n < 0 ⇒ LHS < 0 ⇒ RHS < 0 ⇒ m < 0 (since log3 > 0)
      have hn_negR : (n : ℝ) < 0 := by exact_mod_cast hn_neg
      have hLneg : (n : ℝ) * Real.log (2 : ℝ) < 0 := by
        exact mul_neg_of_neg_of_pos hn_negR hlog2pos
      have hRneg : (m : ℝ) * Real.log (3 : ℝ) < 0 := by simpa [hmul] using hLneg

      have hm_negR : (m : ℝ) < 0 := by
        -- mul_neg_iff returns (m>0 ∧ log3<0) ∨ (m<0 ∧ log3>0)
        have htmp :
            (0 < (m : ℝ) ∧ Real.log (3 : ℝ) < 0) ∨ ((m : ℝ) < 0 ∧ 0 < Real.log (3 : ℝ)) := by
          simpa [mul_neg_iff] using hRneg
        -- flip the ∨ order to match what we want to case on
        have htmp' :
            ((m : ℝ) < 0 ∧ 0 < Real.log (3 : ℝ)) ∨ (0 < (m : ℝ) ∧ Real.log (3 : ℝ) < 0) :=
          Or.comm.mp htmp
        cases htmp' with
        | inl hmn => exact hmn.1
        | inr hp  => exact False.elim (lt_asymm hp.2 hlog3pos)


      have hm_negZ : m < 0 := by exact_mod_cast hm_negR

      -- Work with N = toNat (-n), M = toNat (-m)
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
          exact (by simpa [hn_castZ] using this)
        have : n = 0 := by simpa using (neg_eq_zero.mp this)
        exact hn0 this

      have hn_castR : (N : ℝ) = ((-n) : ℝ) := by exact_mod_cast hn_castZ
      have hm_castR : (M : ℝ) = ((-m) : ℝ) := by exact_mod_cast hm_castZ

      -- negate hmul: (-n)*log2 = (-m)*log3
      have hmul' : ((-n) : ℝ) * Real.log (2 : ℝ) = ((-m) : ℝ) * Real.log (3 : ℝ) := by
        nlinarith [hmul]

      have hmulNM : (N : ℝ) * Real.log (2 : ℝ) = (M : ℝ) * Real.log (3 : ℝ) := by
        simpa [hn_castR, hm_castR] using hmul'

      have hexpNM :
          Real.exp ((N : ℝ) * Real.log (2 : ℝ)) =
          Real.exp ((M : ℝ) * Real.log (3 : ℝ)) := by
        simpa using congrArg Real.exp hmulNM

      have hpowR : (2 : ℝ) ^ N = (3 : ℝ) ^ M := by
        simpa [exp_nat_mul_log (a := (2 : ℝ)) h2pos,
               exp_nat_mul_log (a := (3 : ℝ)) h3pos] using hexpNM

      have hpowN : (2 : ℕ) ^ N = (3 : ℕ) ^ M := by
        have hcast : ((2 : ℕ) ^ N : ℝ) = ((3 : ℕ) ^ M : ℝ) := by
          simpa [Nat.cast_pow, Nat.cast_ofNat] using hpowR
        exact_mod_cast hcast

      exact ⟨M, N, hN0, hpowN⟩

/--
Final lemma:

  `NotRat (log 2 / log 3)`
-/
theorem log2_log3_notRat : NotRat (Real.log (2 : ℝ) / Real.log (3 : ℝ)) := by
  intro h
  rcases h with ⟨m, n, hn0, hrat⟩
  rcases log2_log3_rat_imp_pow_eq (m := m) (n := n) hn0 hrat with ⟨M, N, hN0, hMN⟩

  -- N ≠ 0 ⇒ N = k+1 ⇒ 2 ∣ 2^N
  rcases Nat.exists_eq_succ_of_ne_zero hN0 with ⟨k, hk⟩
  have h2dvd : (2 : ℕ) ∣ (2 : ℕ) ^ N := by
    subst hk
    refine ⟨(2 : ℕ) ^ k, ?_⟩
    simp [pow_succ, Nat.mul_comm, Nat.mul_assoc]

  -- transport through equality: 2 ∣ 3^M
  have h2dvd3 : (2 : ℕ) ∣ (3 : ℕ) ^ M := by
    simpa [hMN] using h2dvd

  have hmod0 : ((3 : ℕ) ^ M) % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 h2dvd3
  have hmod1 : ((3 : ℕ) ^ M) % 2 = 1 := pow3_mod2 M
  have : (0 : ℕ) = 1 := by
    -- hmod0 : (3^M) % 2 = 0, hmod1 : (3^M) % 2 = 1
    -- turn hmod0 into "… = 1" by rewriting, then simp
    simpa [hmod1] using hmod0
  exact Nat.zero_ne_one this

end PrimeWitness
end Cancellation
end Hyperlocal
