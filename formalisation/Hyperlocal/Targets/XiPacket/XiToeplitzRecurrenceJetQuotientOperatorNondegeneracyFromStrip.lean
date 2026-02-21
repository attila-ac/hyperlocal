/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip.lean

  Theorem-level discharge of the leading recurrence coefficient nondegeneracy

    JetQuotOp.aRk1 s 0 ≠ 0

  from explicit **critical strip** bounds.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace JetQuotOp

/--
Explicit real formula for `σ3` in terms of `x = Re(ρ)` and `y = Im(ρ)`.

Proved by `Complex.ext` on `re`/`im` (Lean 4.23 `ext` sometimes won’t find ℂ ext).
-/
lemma σ3_eq_two_mul_y2_add_x1x (s : _root_.Hyperlocal.OffSeed Xi) :
    σ3 s = ((2 * (s.ρ.im ^ 2 + s.ρ.re * (1 - s.ρ.re)) : ℝ) : ℂ) := by
  classical
  cases hρ : s.ρ with
  | mk x y =>
    apply Complex.ext
    ·
      simp [σ3, r1, r2, r3, r4,
        rho, rhoStar, rhoHat, rhoHatStar,
        hρ, sub_eq_add_neg, pow_two]
      ring
    ·
      simp [σ3, r1, r2, r3, r4,
        rho, rhoStar, rhoHat, rhoHatStar,
        hρ, sub_eq_add_neg, pow_two]
      ring

end JetQuotOp

/-- Strip-based nondegeneracy: `aRk1 s 0 ≠ 0`. -/
theorem a0_ne_zero_of_strip (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    JetQuotOp.aRk1 (s : _root_.Hyperlocal.OffSeed Xi) 0 ≠ (0 : ℂ) := by
  classical

  set t : ℝ := (s.ρ.im ^ 2 + s.ρ.re * (1 - s.ρ.re)) with ht

  have hx : 0 < s.ρ.re := s.hRe_pos
  have hx1 : s.ρ.re < 1 := s.hRe_lt_one
  have hy : s.ρ.im ≠ 0 := (s : _root_.Hyperlocal.OffSeed Xi).ht

  have hy2_pos : 0 < s.ρ.im ^ 2 := by
    simpa using (sq_pos_of_ne_zero hy)

  have hx1x_pos : 0 < s.ρ.re * (1 - s.ρ.re) := by
    have h1mx : 0 < (1 - s.ρ.re) := sub_pos.mpr hx1
    exact mul_pos hx h1mx

  have ht_pos : 0 < t := by
    simpa [ht] using add_pos hy2_pos hx1x_pos

  have ht_ne : (2 * t : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) ht_pos)

  have hσ3 : JetQuotOp.σ3 (s : _root_.Hyperlocal.OffSeed Xi) = ((2 * t : ℝ) : ℂ) := by
    simpa [ht] using (JetQuotOp.σ3_eq_two_mul_y2_add_x1x (s := (s : _root_.Hyperlocal.OffSeed Xi)))

  have hσ3_ne : JetQuotOp.σ3 (s : _root_.Hyperlocal.OffSeed Xi) ≠ (0 : ℂ) := by
    intro hz
    have hz' : ((2 * t : ℝ) : ℂ) = (0 : ℂ) := by
      simpa [hσ3] using hz
    have : (2 * t : ℝ) = 0 := by
      have := congrArg Complex.re hz'
      simpa using this
    exact ht_ne this

  have hneg : (-JetQuotOp.σ3 (s : _root_.Hyperlocal.OffSeed Xi)) ≠ (0 : ℂ) :=
    neg_ne_zero.mpr hσ3_ne

  simpa [JetQuotOp.aRk1, JetQuotOp.aR] using hneg

end XiPacket
end Targets
end Hyperlocal
