/-
  GrowthOrder.lean
  Minimal growth predicates for entire functions:
  - an "order ≤ 1" exponential-type bound,
  - a "subexponential × polynomial" bound for multiplicative factors.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic  -- for `ring` and `linarith`

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Factorization
import Hyperlocal.FactorizationGofSAnalytic

noncomputable section
open Complex

namespace Hyperlocal
namespace GrowthOrder

/-- Alias: "entire function" as used throughout the project. -/
def EntireFun (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, AnalyticAt ℂ F z

/--
Order ≤ 1 bound (concrete): there exist `A, B ≥ 0` such that
`‖F z‖ ≤ Real.exp (A * ‖z‖ + B)` for all `z`.
-/
def OrderLEOne (F : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z : ℂ, ‖F z‖ ≤ Real.exp (A * ‖z‖ + B)

/-- Bundled witnesses for an order ≤ 1 bound. (This is a `Type`, not a `Prop`.) -/
structure Order1Bound (F : ℂ → ℂ) where
  A : ℝ
  B : ℝ
  hA : 0 ≤ A
  hB : 0 ≤ B
  bound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (A * ‖z‖ + B)

lemma Order1Bound.to_OrderLEOne {F : ℂ → ℂ} (h : Order1Bound F) :
    OrderLEOne F :=
  ⟨h.A, h.B, h.hA, h.hB, h.bound⟩

/--
“Subexponential × polynomial” bound for a factor `W`:
there exist `C, B ≥ 0` and `N : ℕ` such that
`‖W z‖ ≤ C * (1 + ‖z‖)^N * Real.exp B` for all `z`.
-/
structure SubExpPolyBound (W : ℂ → ℂ) where
  C : ℝ
  B : ℝ
  N : ℕ
  hC : 0 ≤ C
  hB : 0 ≤ B
  bound : ∀ z : ℂ, ‖W z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp B

/-- Trivial example: a constant function has a SubExpPolyBound with `N = 0`. -/
def SubExpPolyBound.const (c : ℂ) :
    SubExpPolyBound (fun _ : ℂ => c) := by
  classical
  refine
    { C := ‖c‖
      B := 0
      N := 0
      hC := norm_nonneg _
      hB := le_of_eq rfl
      bound := ?_ }
  intro z
  -- RHS reduces to ‖c‖, so the inequality is trivial.
  simp [pow_zero, Real.exp_zero]

/-! ---------------------------
    Single-factor, reusable bounds
    --------------------------- -/

-- Minimal helpers for a one-factor bound

/-- Crude but handy: `‖s - c‖ ≤ (1 + ‖s‖) * (1 + ‖c‖)`. -/
lemma norm_sub_le_one_add_mul_one_add (s c : ℂ) :
    ‖s - c‖ ≤ (1 + ‖s‖) * (1 + ‖c‖) := by
  -- triangle inequality to `‖s - c‖ ≤ ‖s‖ + ‖c‖`
  have h₁ : ‖s - c‖ ≤ ‖s‖ + ‖c‖ := by
    calc
      ‖s - c‖ = ‖s + (-c)‖ := by simp [sub_eq_add_neg]
      _ ≤ ‖s‖ + ‖-c‖       := norm_add_le _ _
      _ = ‖s‖ + ‖c‖        := by simp
  -- and `(1 + ‖s‖)(1 + ‖c‖) = (‖s‖ + ‖c‖) + (1 + ‖s‖‖c‖) ≥ ‖s‖ + ‖c‖`
  have hs : 0 ≤ ‖s‖ := norm_nonneg _
  have hc : 0 ≤ ‖c‖ := norm_nonneg _
  have h₂' : 0 ≤ (1 : ℝ) + ‖s‖ * ‖c‖ := by
    have : 0 ≤ ‖s‖ * ‖c‖ := mul_nonneg hs hc
    linarith
  have h₂ : ‖s‖ + ‖c‖ ≤ (1 + ‖s‖) * (1 + ‖c‖) := by
    have htmp : (‖s‖ + ‖c‖) ≤ (‖s‖ + ‖c‖) + (1 + ‖s‖ * ‖c‖) := by
      linarith [h₂']
    have hmul :
        (1 + ‖s‖) * (1 + ‖c‖)
          = (‖s‖ + ‖c‖) + (1 + ‖s‖ * ‖c‖) := by
      ring
    -- rewrite the goal's RHS to the sum form and finish with `htmp`
    rw [hmul]
    exact htmp
  exact le_trans h₁ h₂

/-- Helper (ℝ): if `0 ≤ a ≤ b` then `a^k ≤ b^k`. -/
private lemma pow_mono_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    ∀ k : ℕ, a ^ k ≤ b ^ k
  | 0 => by simp
  | Nat.succ k =>
    have ih : a ^ k ≤ b ^ k := pow_mono_nonneg ha hb hab k
    have h1 : a ^ k * a ≤ b ^ k * a :=
      mul_le_mul_of_nonneg_right ih ha
    have h2 : b ^ k * a ≤ b ^ k * b :=
      mul_le_mul_of_nonneg_left hab (by simpa using pow_nonneg hb k)
    -- a^(k+1) = a^k * a, similarly for b
    by
      simpa [pow_succ, mul_assoc] using (le_trans h1 h2)

/-- Raise the previous bound to the k-th power:
    `‖(s - c)^k‖ ≤ ((1 + ‖s‖) * (1 + ‖c‖))^k`. -/
lemma norm_pow_sub_le_one_add_mul_one_add (s c : ℂ) (k : ℕ) :
    ‖(s - c) ^ k‖ ≤ ((1 + ‖s‖) * (1 + ‖c‖)) ^ k := by
  -- base inequality and nonnegativity of both sides
  have base_le : ‖s - c‖ ≤ (1 + ‖s‖) * (1 + ‖c‖) :=
    norm_sub_le_one_add_mul_one_add s c
  have base_nonneg : 0 ≤ ‖s - c‖ := norm_nonneg _
  have rhs_nonneg : 0 ≤ (1 + ‖s‖) * (1 + ‖c‖) := by
    have hs : 0 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    have hc : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
    exact mul_nonneg hs hc
  -- monotonicity of `x ↦ x^k` on `ℝ≥0`
  have hpow : ‖s - c‖ ^ k ≤ ((1 + ‖s‖) * (1 + ‖c‖)) ^ k :=
    pow_mono_nonneg base_nonneg rhs_nonneg base_le k
  -- rewrite `‖(s - c)^k‖` as `‖s - c‖^k`
  have hn : ‖(s - c) ^ k‖ = ‖s - c‖ ^ k := norm_pow (s - c) k
  rw [hn]
  exact hpow

/-- A convenient dominating constant for the quartet centers. -/
private def Mρ (ρ : ℂ) : ℝ :=
  max (1 + ‖ρ‖)
    (max (1 + ‖star ρ‖)
      (max (1 + ‖oneMinus ρ‖)
           (1 + ‖oneMinus (star ρ)‖)))

/-- `Mρ ρ ≥ 0`. -/
private lemma Mρ_nonneg (ρ : ℂ) : 0 ≤ Mρ ρ := by
  have h0 : 0 ≤ 1 + ‖ρ‖ := by linarith [norm_nonneg ρ]
  have hle : (1 + ‖ρ‖) ≤ Mρ ρ := by
    -- leftmost branch of the max
    exact le_max_left _ _
  exact le_trans h0 hle

/-- Each quartet center satisfies `1 + ‖c‖ ≤ Mρ ρ`. -/
private lemma le_Mρ_of_center (ρ c : ℂ)
    (hc : c = ρ ∨ c = star ρ ∨ c = oneMinus ρ ∨ c = oneMinus (star ρ)) :
    1 + ‖c‖ ≤ Mρ ρ := by
  rcases hc with rfl | hc | hc | hc
  · -- c = ρ
    exact le_max_left _ _
  · -- c = star ρ
    subst hc
    have h1 :
        1 + ‖star ρ‖ ≤
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) :=
      le_max_left _ _
    have h2 :
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) ≤
        Mρ ρ :=
      le_max_right _ _
    exact le_trans h1 h2
  · -- c = 1 - ρ
    subst hc
    have h1 :
        1 + ‖oneMinus ρ‖ ≤
        max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖) :=
      le_max_left _ _
    have h2 :
        max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖) ≤
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) :=
      le_max_right _ _
    have h3 :
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) ≤
        Mρ ρ :=
      le_max_right _ _
    exact le_trans h1 (le_trans h2 h3)
  · -- c = 1 - star ρ
    subst hc
    have h1 :
        1 + ‖oneMinus (star ρ)‖ ≤
        max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖) :=
      le_max_right _ _
    have h2 :
        max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖) ≤
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) :=
      le_max_right _ _
    have h3 :
        max (1 + ‖star ρ‖)
            (max (1 + ‖oneMinus ρ‖) (1 + ‖oneMinus (star ρ)‖)) ≤
        Mρ ρ :=
      le_max_right _ _
    exact le_trans h1 (le_trans h2 h3)

/-- Each quartet factor is bounded by `Mρ^k * (1+‖s‖)^k`. -/
private lemma factor_bound_quartet
    (ρ s c : ℂ) (k : ℕ)
    (hc : c = ρ ∨ c = star ρ ∨ c = oneMinus ρ ∨ c = oneMinus (star ρ)) :
    ‖(s - c) ^ k‖ ≤ (Mρ ρ) ^ k * (1 + ‖s‖) ^ k := by
  -- Step 1: raise the crude one-factor bound to the k-th power
  have h₀ : ‖(s - c) ^ k‖ ≤ ((1 + ‖s‖) * (1 + ‖c‖)) ^ k :=
    norm_pow_sub_le_one_add_mul_one_add s c k
  -- Step 2: compare the bases: (1+‖s‖)(1+‖c‖) ≤ (1+‖s‖) * Mρ
  have hs0 : 0 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hc_le : 1 + ‖c‖ ≤ Mρ ρ := by
    -- use the quartet-membership of c
    exact le_Mρ_of_center ρ c hc
  have hbase_le :
      (1 + ‖s‖) * (1 + ‖c‖) ≤ (1 + ‖s‖) * (Mρ ρ) :=
    mul_le_mul_of_nonneg_left hc_le hs0
  have hbase0 : 0 ≤ (1 + ‖s‖) * (1 + ‖c‖) := by
    have hc0 : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
    exact mul_nonneg hs0 hc0
  have hbaseM0 : 0 ≤ (1 + ‖s‖) * (Mρ ρ) :=
    mul_nonneg hs0 (Mρ_nonneg ρ)
  -- Step 3: monotonicity of x ↦ x^k on ℝ≥0
  have h₁ :
      ((1 + ‖s‖) * (1 + ‖c‖)) ^ k ≤ ((1 + ‖s‖) * (Mρ ρ)) ^ k :=
    pow_mono_nonneg hbase0 hbaseM0 hbase_le k
  -- Step 4: assemble and rewrite ((1+‖s‖)*M)^k as product of powers
  have := le_trans h₀ h₁
  -- ((1+‖s‖) * Mρ)^k = (1+‖s‖)^k * (Mρ)^k; commute to match the stated RHS
  simpa [mul_pow, mul_comm] using this

/-- Subexp–poly bound for the quartet evaluation:
    `‖(Rρk ρ k).eval s‖ ≤ (Mρ ρ)^(4k) * (1 + ‖s‖)^(4k)`.
    Packaged as a `SubExpPolyBound` with `B = 0`, `C = (Mρ ρ)^(4k)`, `N = 4k`. -/
def subExpPoly_eval_Rρk (ρ : ℂ) (k : ℕ) :
    SubExpPolyBound (fun s : ℂ => (Hyperlocal.Factorization.Rρk ρ k).eval s) := by
  classical
  refine
    { C := (Mρ ρ) ^ (4 * k)
      B := 0
      N := 4 * k
      hC := pow_nonneg (Mρ_nonneg ρ) _
      hB := le_of_eq rfl
      bound := ?_ }
  intro s

  -- Name the four factors
  set f1 : ℂ := (s - ρ) ^ k with hf1def
  set f2 : ℂ := (s - star ρ) ^ k with hf2def
  set f3 : ℂ := (s - oneMinus ρ) ^ k with hf3def
  set f4 : ℂ := (s - oneMinus (star ρ)) ^ k with hf4def

  -- Explicit factorization (as (f1 * f2) * (f3 * f4))
  have hR :
      (Hyperlocal.Factorization.Rρk ρ k).eval s
        = (f1 * f2) * (f3 * f4) := by
    have := Hyperlocal.FactorizationAnalytic.eval_Rρk_explicit ρ s k
    simpa [hf1def, hf2def, hf3def, hf4def, mul_assoc] using this

  -- Norm(product) ≤ product of norms, twice
  have h_le₀ :
      ‖(Hyperlocal.Factorization.Rρk ρ k).eval s‖
        ≤ ‖f1 * f2‖ * ‖f3 * f4‖ := by
    simpa [hR] using norm_mul_le (f1 * f2) (f3 * f4)
  have h12 : ‖f1 * f2‖ ≤ ‖f1‖ * ‖f2‖ := norm_mul_le f1 f2
  have h34 : ‖f3 * f4‖ ≤ ‖f3‖ * ‖f4‖ := norm_mul_le f3 f4
  -- side conditions for `mul_le_mul`
  have h_nonneg_c : 0 ≤ ‖f3 * f4‖ := norm_nonneg _
  have h_nonneg_b : 0 ≤ ‖f1‖ * ‖f2‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_le₁ :
      ‖f1 * f2‖ * ‖f3 * f4‖
        ≤ (‖f1‖ * ‖f2‖) * (‖f3‖ * ‖f4‖) :=
    mul_le_mul h12 h34 h_nonneg_c h_nonneg_b
  have h_prod_norm :
      ‖(Hyperlocal.Factorization.Rρk ρ k).eval s‖
        ≤ (‖f1‖ * ‖f2‖) * (‖f3‖ * ‖f4‖) :=
    le_trans h_le₀ h_le₁

  -- Set T := (Mρ ρ)^k * (1 + ‖s‖)^k
  set T : ℝ := (Mρ ρ) ^ k * (1 + ‖s‖) ^ k with hTdef
  have T_nonneg : 0 ≤ T :=
    mul_nonneg (pow_nonneg (Mρ_nonneg ρ) _) (pow_nonneg (by linarith [norm_nonneg s]) _)

  -- Each factor ≤ T via the quartet factor lemma
  have hf1 : ‖f1‖ ≤ T := by
    simpa [hf1def, hTdef] using
      factor_bound_quartet ρ s ρ k (Or.inl rfl)
  have hf2 : ‖f2‖ ≤ T := by
    simpa [hf2def, hTdef] using
      factor_bound_quartet ρ s (star ρ) k (Or.inr (Or.inl rfl))
  have hf3 : ‖f3‖ ≤ T := by
    simpa [hf3def, hTdef] using
      factor_bound_quartet ρ s (oneMinus ρ) k (Or.inr (Or.inr (Or.inl rfl)))
  have hf4 : ‖f4‖ ≤ T := by
    simpa [hf4def, hTdef] using
      factor_bound_quartet ρ s (oneMinus (star ρ)) k (Or.inr (Or.inr (Or.inr rfl)))

  -- Two-by-two products ≤ T*T
  have h12' : ‖f1‖ * ‖f2‖ ≤ T * T :=
    mul_le_mul hf1 hf2 (norm_nonneg _) T_nonneg
  have h34' : ‖f3‖ * ‖f4‖ ≤ T * T :=
    mul_le_mul hf3 hf4 (norm_nonneg _) T_nonneg

  -- Multiply the two bounds
  have hTT :
      (‖f1‖ * ‖f2‖) * (‖f3‖ * ‖f4‖) ≤ (T * T) * (T * T) :=
    mul_le_mul h12' h34'
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))  -- 0 ≤ ‖f3‖ * ‖f4‖
      (mul_nonneg T_nonneg T_nonneg)                -- 0 ≤ T * T

  have hFinal :
      ‖(Hyperlocal.Factorization.Rρk ρ k).eval s‖
        ≤ (T * T) * (T * T) :=
    le_trans h_prod_norm hTT

  -- Expand (T*T)*(T*T) as (Mρ ρ)^(4k) * (1+‖s‖)^(4k)
  set A : ℝ := (Mρ ρ) ^ k
  set B : ℝ := (1 + ‖s‖) ^ k
  have T_def : T = A * B := by simpa [A, B, hTdef]
  have TT : T * T = A^2 * B^2 := by
    simp [T_def, pow_two, mul_pow, mul_comm, mul_left_comm, mul_assoc]

  -- *** this is the injected little algebra block ***
  -- Expand (T*T)*(T*T) as (Mρ ρ)^(4k) * (1+‖s‖)^(4k)
  set A : ℝ := (Mρ ρ) ^ k
  set B : ℝ := (1 + ‖s‖) ^ k
  have T_def : T = A * B := by simpa [A, B, hTdef]
  have TT : T * T = A^2 * B^2 := by
    simp [T_def, pow_two, mul_pow, mul_comm, mul_left_comm, mul_assoc]

  have expandTT :
      (T * T) * (T * T) = A ^ 4 * B ^ 4 := by
    have h4 : (4 : ℕ) = 2 + 2 := by decide
    calc
      (T * T) * (T * T)
          = (A^2 * B^2) * (A^2 * B^2) := by simpa [TT]
      _ = (A^2 * A^2) * (B^2 * B^2) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      _ = A^(2+2) * B^(2+2) := by
        simp [pow_add, pow_two]
      _ = A^4 * B^4 := by
        simpa [h4]

  -- Use the expansion and then fold A^4, B^4 back to (4*k)
  have : ‖(Hyperlocal.Factorization.Rρk ρ k).eval s‖
      ≤ A ^ 4 * B ^ 4 := by
    simpa [expandTT] using hFinal
  have : ‖(Hyperlocal.Factorization.Rρk ρ k).eval s‖
      ≤ (Mρ ρ) ^ (4 * k) * (1 + ‖s‖) ^ (4 * k) := by
    -- (x^k)^4 = x^(4*k)
    simpa [A, B, pow_mul, Nat.mul_comm, Nat.mul_left_comm,
           mul_comm, mul_left_comm, mul_assoc] using this

  -- Conclude in the SubExpPolyBound shape
  simpa [Real.exp_zero]


end GrowthOrder
end Hyperlocal
end
