-- Hyperlocal/Appendix/InstabilityK1_Small.lean
/-
  Small-t regime for k = 1 (numeric scaffolding + green stubs)

  What this file provides right now:
  • The same “keep the pipeline green” stubs you already had.
  • Clean numerical lemmas for the small-t side:
        polyR R := 1 + R + R^2   (positivity for R>1)
        gapSmall A R := R^2 - |A| * R^3 = R^2 * (1 - |A|R)  (positivity if |A|R<1)
        T_small_of_R A R C := gapSmall / (2 * (C * polyR))
    and the key budgeting inequality
        (C * t) * polyR R ≤ gapSmall A R / 2    whenever  0 ≤ t ≤ T_small_of_R …

  Next micro-step (separate lemma): combine this with a circle bound
  ‖E‖ ≤ (C * t) * polyR R to get ‖E‖ ≤ gapSmall/2 on |z|=R, then your local Rouché axiom.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Appendix.InstabilityK1_Fillers

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Small

/-- (placeholder) any 1 < R < |1/A| later; pick anything now -/
def R_small (_A : ℝ) : ℝ := (3 : ℝ) / 2

/-- (placeholder) perturbation bound constant; wire real bound later -/
def C_small (_A : ℝ) : ℝ := 1

/-- (placeholder) small threshold; pick a clean positive number -/
def t1_small (_A : ℝ) : ℝ := 1

/-- Small-t instability (stub). Replace body by the Rouché proof later. -/
theorem unstable_small (A : ℝ) :
  ∀ {t : ℝ}, 0 < t → t ≤ t1_small A → UnstableHom 1 A t := by
  intro _t _ _
  exact ⟨trivial⟩

/-- Packaged small-t hypothesis for the aggregator. -/
def SmallHyp_pkg (A : ℝ) : SmallHyp A (t1_small A) :=
{ h0 := by
    -- 0 < 1
    simpa [t1_small] using (zero_lt_one : (0 : ℝ) < 1),
  prove := by
    intro t ht htle; exact unstable_small A ht htle }

/- -------------------------------------------------------------------------- -/
/-           Minimal numerical core for the small-t Rouché step               -/
/- -------------------------------------------------------------------------- -/

def polyR (R : ℝ) : ℝ := 1 + R + R^2

/-- For `R > 1` we have `polyR R ≥ 3`, hence `polyR R > 0`. -/
lemma polyR_pos_of_one_lt {R : ℝ} (R_gt1 : 1 < R) : 0 < polyR R := by
  have hRge1 : (1 : ℝ) ≤ R := le_of_lt R_gt1
  have hRnn  : 0 ≤ R      := le_trans (by norm_num : (0:ℝ) ≤ 1) hRge1
  -- show 3 ≤ 1 + R + R^2
  have three_le : (3 : ℝ) ≤ polyR R := by
    -- (1+1+1) ≤ (1 + R + R^2)
    have base : (1 : ℝ) + 1 + 1 ≤ 1 + R + R^2 :=
      add_le_add (add_le_add le_rfl hRge1)
        (le_trans hRge1 (by
          -- R ≤ R^2 since R ≥ 1
          simpa [one_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]
            using (mul_le_mul_of_nonneg_left hRge1 hRnn)))
    have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    simpa [polyR, add_assoc, add_comm, add_left_comm, h3] using base
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) three_le

/-- the “small-t gap” against `-z^2`:  `R^2 - |A| R^3`. -/
def gapSmall (A R : ℝ) : ℝ := R^2 - |A| * R^3

/-- Factorisation and positivity of the small-t gap when `1 < R` and `|A| R < 1`. -/
lemma gapSmall_pos {A R : ℝ} (R_gt1 : 1 < R) (hARlt1 : |A| * R < 1) :
  0 < gapSmall A R := by
  have Rpos  : 0 < R   := lt_trans (by norm_num) R_gt1
  have R2pos : 0 < R^2 := by simpa [pow_two] using (pow_pos Rpos 2)
  have fac : gapSmall A R = R^2 * (1 - |A| * R) := by
    have : R^3 = R^2 * R := by simpa [pow_succ, pow_two]
    calc
      R^2 - |A| * R^3
          = R^2 - |A| * (R^2 * R) := by simpa [this]
      _   = R^2 - R^2 * (|A| * R) := by ring
      _   = R^2 * (1 - |A| * R)   := by ring
  have : 0 < 1 - |A| * R := sub_pos.mpr hARlt1
  have : 0 < R^2 * (1 - |A| * R) := mul_pos R2pos this
  simpa [gapSmall, fac] using this

/-- Convenient strict inequality from the gap: `|A| R^3 < R^2`. -/
lemma small_gap_ineq {A R : ℝ} (R_gt1 : 1 < R) (hARlt1 : |A| * R < 1) :
  |A| * R^3 < R^2 := by
  -- `gapSmall_pos` says `0 < R^2 - |A| R^3`; turn that into `|A| R^3 < R^2`.
  have hg : 0 < gapSmall A R := gapSmall_pos (A:=A) R_gt1 hARlt1
  simpa [gapSmall] using (sub_pos.mp hg)

/-- small-t threshold in the *linear* decay setting:
    if `‖E‖ ≤ (C * t) * polyR R` on `|z|=R`, then taking
      `t ≤ T_small_of_R := gapSmall / (2 * (C * polyR))`
    yields `‖E‖ ≤ gapSmall/2`. -/
def T_small_of_R (A R C : ℝ) : ℝ :=
  gapSmall A R / (2 * (C * polyR R))

/-- With `1 < R`, `|A| R < 1` and `C > 0`, the threshold is positive. -/
lemma T_small_of_R_pos {A R C : ℝ}
  (R_gt1 : 1 < R) (hARlt1 : |A| * R < 1) (C_pos : 0 < C) :
  0 < T_small_of_R A R C := by
  have gap_pos  : 0 < gapSmall A R := gapSmall_pos (A:=A) R_gt1 hARlt1
  have poly_pos : 0 < polyR R      := polyR_pos_of_one_lt R_gt1
  have denom_pos : 0 < 2 * (C * polyR R) :=
    mul_pos (by norm_num) (mul_pos C_pos poly_pos)
  simpa [T_small_of_R] using div_pos gap_pos denom_pos

/-- Key budget inequality for the small-t regime:
    if `0 ≤ t ≤ T_small_of_R`, then `(C * t) * polyR R ≤ gapSmall/2`. -/
lemma budget_le_half_gap {A R C t : ℝ}
  (R_gt1 : 1 < R) (hARlt1 : |A| * R < 1) (C_pos : 0 < C)
  (_t_nonneg : 0 ≤ t) (hle : t ≤ T_small_of_R A R C) :
  (C * t) * polyR R ≤ gapSmall A R / 2 := by
  -- abbreviations
  set P := polyR R with hP
  have P_pos  : 0 < P := by simpa [hP] using polyR_pos_of_one_lt (R:=R) R_gt1
  have CP_pos : 0 < C * P := mul_pos C_pos P_pos
  have CP_nn  : 0 ≤ C * P := le_of_lt CP_pos
  have CP_ne  : C * P ≠ 0 := ne_of_gt CP_pos
  -- multiply `t ≤ gap/(2*(C*P))` by the nonneg factor `C*P`
  have hmul :
      (C * P) * t ≤ (C * P) * (gapSmall A R / (2 * (C * P))) :=
    mul_le_mul_of_nonneg_left hle CP_nn
  -- simplify RHS: (C*P) * (gap / (2*(C*P))) = gap / 2
  have rhs_simp :
      (C * P) * (gapSmall A R / (2 * (C * P)))
        = gapSmall A R / 2 := by
    -- step 1: turn `a * (b/d)` into `((a*b)/d)`
    have h₁ :
        (C * P) * (gapSmall A R / (2 * (C * P)))
          = ((C * P) * (gapSmall A R)) / (2 * (C * P)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using (mul_div_assoc (C * P) (gapSmall A R) (2 * (C * P))).symm
    -- step 2: commute numerator to `b * a`
    have h₂ :
        ((C * P) * (gapSmall A R)) / (2 * (C * P))
          = (gapSmall A R * (C * P)) / (2 * (C * P)) := by
      simpa [mul_comm, mul_left_comm]
    -- step 3: cancel `(C*P)` using `mul_div_mul_left`
    have h₃ :
        (gapSmall A R * (C * P)) / (2 * (C * P))
          = gapSmall A R / 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (mul_div_mul_left (gapSmall A R) (2 : ℝ) (C * P) CP_ne)
    exact h₁.trans (h₂.trans h₃)
  -- conclude
  have hmul' : (C * P) * t ≤ gapSmall A R / 2 := by
    simpa [rhs_simp] using hmul
  simpa [hP, mul_comm, mul_left_comm, mul_assoc] using hmul'




end Small
end InstabilityK1
end Cancellation
end Hyperlocal
end section
