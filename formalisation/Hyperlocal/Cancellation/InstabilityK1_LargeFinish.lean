-- Hyperlocal/Cancellation/InstabilityK1_LargeFinish.lean
/-
  Finish the large-t route:
  decay ⇒ boundary dominance ⇒ local Rouché ⇒ outside-unit root ⇒ UnstableHom.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Hyperlocal.Cancellation.InstabilityK1_Large
import Hyperlocal.Cancellation.RoucheCircle

noncomputable section
open Complex

namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Large

/-- From `DomAtCircle` get the strict boundary inequality `‖f - g‖ < ‖g‖`
    needed by the local Rouché axiom, where `g z = (A:ℂ) * z^3 - z^2`. -/
private lemma boundary_strict_ineq
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R t : ℝ}
  (h : DomAtCircle P1 A R t) :
  ∀ z : ℂ, ‖z‖ = R →
    ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
      < ‖(A : ℂ) * z ^ 3 - z ^ 2‖ := by
  intro z hz
  -- Dominance statement from the large file:
  --   ‖A z^3‖ > ‖z^2‖ + ‖E‖ with E := f - g
  have H :=
    strict_dominance_on_circle (P1:=P1) (A:=A) (R:=R) (t:=t) h (z:=z) hz
  -- Put it as: ‖E‖ < ‖A z^3‖ - ‖z^2‖
  have H' :
      ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
        < ‖(A : ℂ) * z ^ 3‖ - ‖z ^ 2‖ := by
    have H2 :
        ‖z ^ 2‖ + ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
          < ‖(A : ℂ) * z ^ 3‖ := by
      simpa [add_comm] using H
    -- cancel the common ‖z^2‖ on both sides
    have : ‖z ^ 2‖ + ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
              < ‖z ^ 2‖ + (‖(A : ℂ) * z ^ 3‖ - ‖z ^ 2‖) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H2
    exact (add_lt_add_iff_left (‖z ^ 2‖)).1 this

  /- We want to derive  ‖E‖ < ‖g‖.
     We'll (i) add ‖z‖^2 on both sides of H' after rewriting ‖A z^3‖, ‖z^2‖
     and then (ii) compare with the triangle inequality in plus-form:
         ‖A z^3‖ ≤ ‖A z^3 - z^2‖ + ‖z^2‖.
  -/

  -- Algebraic norm rewrites to |A| * ‖z‖^3 and ‖z‖^2
  have hz2 : ‖z ^ 2‖ = ‖z‖ ^ 2 := by
    -- ‖z^2‖ = ‖z‖ * ‖z‖
    have : ‖z ^ 2‖ = ‖z‖ * ‖z‖ := by
      simpa [pow_two] using (norm_mul z z)
    simpa [pow_two] using this
  have hz3 : ‖z ^ 3‖ = ‖z‖ ^ 3 := by
    -- ‖z^3‖ = ‖z^2‖ * ‖z‖, and ‖z^2‖ = ‖z‖^2
    have : ‖z ^ 3‖ = ‖z ^ 2‖ * ‖z‖ := by
      simpa [pow_succ] using (norm_mul (z ^ 2) z)
    simpa [hz2] using this
  have hA : ‖(A : ℂ)‖ = |A| := by simpa using Complex.norm_ofReal A
  have normAz3 : ‖(A : ℂ) * z ^ 3‖ = |A| * ‖z‖ ^ 3 := by
    simpa [hA, hz3, mul_comm] using (norm_mul ((A : ℂ)) (z ^ 3))

  -- Add ‖z‖^2 to both sides of H' (after rewriting) to get:
  --   ‖E‖ + ‖z‖^2 < |A| * ‖z‖^3
  have step1 :
      ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖ + ‖z‖ ^ 2
        < |A| * ‖z‖ ^ 3 := by
    have H'' :
        ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
          < (|A| * ‖z‖ ^ 3) - (‖z‖ ^ 2) := by
      simpa [normAz3, hz2] using H'
    -- add ‖z‖^2 on both sides and cancel
    have := add_lt_add_right H'' (‖z‖ ^ 2)
    -- (|A|‖z‖^3 - ‖z‖^2) + ‖z‖^2 = |A|‖z‖^3
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  -- Triangle in plus-form, rewritten to |A| * ‖z‖^3 and ‖z‖^2:
  have step2 :
      |A| * ‖z‖ ^ 3 ≤ ‖(A : ℂ) * z ^ 3 - z ^ 2‖ + ‖z‖ ^ 2 := by
    -- base: ‖A z^3‖ ≤ ‖A z^3 - z^2‖ + ‖z^2‖
    have base := norm_sub_norm_le ((A : ℂ) * z ^ 3) (z ^ 2)
    simpa [normAz3, hz2] using base

  -- Chain them:  ‖E‖ + ‖z‖^2 < ‖g‖ + ‖z‖^2
  have step3 :
      ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖ + ‖z‖ ^ 2
        < ‖(A : ℂ) * z ^ 3 - z ^ 2‖ + ‖z‖ ^ 2 :=
    lt_of_lt_of_le step1 step2

  -- Cancel the common + ‖z‖^2 (commute to the left then use `lt_of_add_lt_add_left`)
  have step3' :
      ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
        < ‖(A : ℂ) * z ^ 3 - z ^ 2‖ := by
    -- rewrite both sides as  ‖z‖^2 + (…)
    have : ‖z‖ ^ 2 + ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
              < ‖z‖ ^ 2 + ‖(A : ℂ) * z ^ 3 - z ^ 2‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using step3
    exact (lt_of_add_lt_add_left this)
  exact step3'

/-- **Large-t: decay ⇒ dominance ⇒ Rouché ⇒ unstable root**. -/
theorem unstable_large_with_decay_rouche
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R K : ℝ}
  (A_ne0    : A ≠ 0)
  (hA_lt1   : |A| < 1)
  (R_gt1    : 1 < R)
  (one_lt_AR : 1 < |A| * R)
  (K_nonneg : 0 ≤ K)
  (hE_decay :
    ∀ {t : ℝ}, 0 < t → ∀ {z : ℂ}, ‖z‖ = R →
      ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
        ≤ (K / t) * (1 + R + R ^ 2))
  (hR_big   : max 1 (|1 / A|) < R)
  (mk_unstable :
    ∀ {t : ℝ}, (∃ z : ℂ, 1 < ‖z‖ ∧ P1 A t z = 0) → UnstableHom 1 A t)
  : ∀ {t : ℝ}, T_of_R A R K ≤ t → UnstableHom 1 A t := by
  intro t ht
  -- dominance from decay
  have hDom :
      DomAtCircle P1 A R t :=
    DomAtCircle_for_all_large_t
      (P1:=P1) (A:=A) (R:=R) (K:=K)
      A_ne0 R_gt1 one_lt_AR K_nonneg hE_decay (t:=t) ht
  -- boundary inequality for (axiomatic) local Rouché
  have hbdry :
      ∀ z : ℂ, ‖z‖ = R →
        ‖(P1 A t z) - ((A : ℂ) * z ^ 3 - z ^ 2)‖
          < ‖(A : ℂ) * z ^ 3 - z ^ 2‖ :=
    boundary_strict_ineq (P1:=P1) (A:=A) (R:=R) (t:=t) hDom
  -- pick r with 1 < r < R
  let r : ℝ := (1 + R) / 2
  -- first hop: 2 < R + 1  (write it as a calc to avoid coercion hiccups)
  have h2R1 : (2 : ℝ) < R + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _       < R + 1 := add_lt_add_right R_gt1 1
  -- second hop: commute to get 2 < 1 + R
  have h2 : (2 : ℝ) < 1 + R := by
    simpa [add_comm] using h2R1
  -- hence 1 < r
  have hr_gt1 : 1 < r := by
    have := div_lt_div_of_pos_right h2 (by norm_num : (0:ℝ) < 2)
    simpa [r] using this
  -- also r < R
  have hr_ltR : r < R := by
    -- from 1 < R ⇒ 1 + R < R + R, then divide by 2
    have hsum : 1 + R < R + R := by
      simpa [two_mul] using (add_lt_add_right R_gt1 R)
    have := div_lt_div_of_pos_right hsum (by norm_num : (0:ℝ) < 2)
    simpa [r, two_mul] using this
  -- a point with 1 < ‖·‖ < R
  let zStar : ℂ := (r : ℝ)
  have r_nonneg : 0 ≤ r := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hr_gt1)
  have hzStar_gt1 : 1 < ‖zStar‖ := by
    have : 1 < (|r|) := by simpa [abs_of_nonneg r_nonneg] using hr_gt1
    exact (by simpa [zStar, Complex.norm_real] using this)
  have hzStar_in  : ‖zStar‖ < R := by
    have : (|r|) < R := by simpa [abs_of_nonneg r_nonneg] using hr_ltR
    exact (by simpa [zStar, Complex.norm_real] using this)
  -- Rouché ⇒ a zero with ‖z‖ > 1
  obtain ⟨z0, hz0_in, hz0_gt1, hz0_root⟩ :=
    Hyperlocal.Cancellation.rouche_on_circle_exists_big_root
      (cnorm    := fun z => ‖z‖)
      (f        := fun z => P1 A t z)
      (A        := A)
      (R        := R)
      (onCircle := fun z => ‖z‖ = R)
      (inside   := fun z => ‖z‖ < R)
      (hR       := lt_trans (by norm_num) R_gt1)
      (hbdry    := by intro z hz; exact hbdry z hz)  -- (avoid linter: use `exact`)
      (hA_lt1   := hA_lt1)
      (annulus  :=
        ⟨ (by intro z; rfl),             -- onCircle z ↔ ‖z‖ = R
          (by intro z; rfl),             -- inside   z ↔ ‖z‖ < R
          ⟨ zStar, hzStar_in, hzStar_gt1 ⟩,
          hR_big ⟩)
  -- outside-unit-circle root ⇒ project witness
  exact mk_unstable (t:=t) ⟨z0, by exact hz0_gt1, by simpa [hz0_root]⟩

end Large
end InstabilityK1
end Cancellation
end Hyperlocal
