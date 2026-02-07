/-
  Hyperlocal/Targets/XiPacket/XiWindowAnchorNonvanishing.lean

  Plan C++: isolate the last explicit semantic ingredient used to make κ ≠ 0.

  Pure algebra:
    Re(Xi(sc s)) = anchorScalar(s) * Re(completedRiemannZeta(sc s)),
  where anchorScalar(s) = -(1/4 + (t s)^2) is a nonzero real scalar.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/-- The real scalar multiplying Λ(sc). -/
def anchorScalar (s : Hyperlocal.OffSeed Xi) : ℝ :=
  -((1 : ℝ)/4 + (t s)^2)

/-- Real scalar times complex: real part. -/
lemma re_ofReal_mul (a : ℝ) (z : ℂ) : (((a : ℂ) * z).re) = a * z.re := by
  simp [Complex.mul_re]

/-- The anchor factor `sc(s) * (sc(s) - 1)` is the real number `anchorScalar s`. -/
lemma sc_mul_sc_sub_one (s : Hyperlocal.OffSeed Xi) :
    sc s * (sc s - 1) = (anchorScalar s : ℂ) := by
  -- prove equality in ℂ by re/im components
  refine Complex.ext ?_ ?_
  · -- real part
    simp [sc, t, anchorScalar, sub_eq_add_neg, Complex.mul_re, Complex.mul_im, pow_two]
    ring_nf
  · -- imaginary part
    simp [sc, t, anchorScalar, sub_eq_add_neg, Complex.mul_re, Complex.mul_im, pow_two]
    ring_nf

/-- Closed-form for Xi on the critical-line anchor: Xi(sc) is a real scalar times Λ(sc). -/
lemma Xi_sc_eq_real_mul_completed (s : Hyperlocal.OffSeed Xi) :
    Xi (sc s) = (anchorScalar s : ℂ) * completedRiemannZeta (sc s) := by
  -- Xi z = z*(z-1)*Λ(z)
  simpa [Xi, Hyperlocal.xi, sc_mul_sc_sub_one (s := s)]

/-- Real-part reduction: `Re(Xi(sc)) = anchorScalar(s) * Re(Λ(sc))`. -/
lemma Xi_sc_re_eq (s : Hyperlocal.OffSeed Xi) :
    (Xi (sc s)).re = (anchorScalar s) * (completedRiemannZeta (sc s)).re := by
  have h := congrArg Complex.re (Xi_sc_eq_real_mul_completed (s := s))
  simpa [re_ofReal_mul] using h

/-- The scalar `anchorScalar` is nonzero (purely algebraic). -/
lemma anchorScalar_ne_zero (u : ℝ) : (-( (1 : ℝ)/4 + u^2 )) ≠ 0 := by
  have hquarter : (0 : ℝ) < (1 : ℝ)/4 := by norm_num
  have hpos : (0 : ℝ) < (1 : ℝ)/4 + u^2 := by
    nlinarith [sq_nonneg u, hquarter]
  exact neg_ne_zero.mpr (ne_of_gt hpos)

/--
Canonical form of the remaining semantic target.

Stable form: `Re(Λ(sc)) ≠ 0`.
-/
def XiAnchorNonvanishing (s : Hyperlocal.OffSeed Xi) : Prop :=
  (completedRiemannZeta (sc s)).re ≠ 0

/-- `XiAnchorNonvanishing` implies the original target `(Xi(sc)).re ≠ 0`. -/
theorem Xi_sc_re_ne_zero_of_anchor (s : Hyperlocal.OffSeed Xi)
    (h : XiAnchorNonvanishing s) : (Xi (sc s)).re ≠ 0 := by
  have ha : (anchorScalar s) ≠ 0 := by
    -- unfold anchorScalar and use the generic lemma
    simpa [anchorScalar] using (anchorScalar_ne_zero (u := t s))
  -- IMPORTANT: use `rw`, not `simp`, to avoid rewriting `a*b ≠ 0` into a conjunction.
  rw [Xi_sc_re_eq (s := s)]
  exact mul_ne_zero ha h

/--
THE LAST semantic cliff (explicit and recognizable).

For now, keep it as a single axiom in the reduced/stable form.
-/
axiom xiAnchorNonvanishing (s : Hyperlocal.OffSeed Xi) : XiAnchorNonvanishing s

/-- Convenience: recover the original shape `(Xi(sc)).re ≠ 0` from the axiom. -/
theorem xi_sc_re_ne_zero (s : Hyperlocal.OffSeed Xi) : (Xi (sc s)).re ≠ 0 :=
  Xi_sc_re_ne_zero_of_anchor (s := s) (xiAnchorNonvanishing (s := s))

end XiPacket
end Targets
end Hyperlocal
