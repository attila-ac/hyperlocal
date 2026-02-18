/-
  Hyperlocal/Targets/XiPacket/XiWindowAnchorNonvanishing.lean

  Plan C++ (Route B): keep the anchor algebra, but remove the hard zeta-specific
  nonvanishing axiom. The remaining semantic insertion point is jet-nonflatness
  at the anchor, imported from `XiJetNonflatOfAnalytic`.

  Pure algebra:
    Re(Xi(sc s)) = anchorScalar(s) * Re(completedRiemannZeta(sc s)),
  where anchorScalar(s) = -(1/4 + (t s)^2) is a nonzero real scalar.

  The file also provides the Re/Im split interface:
    `xiJetNonflat_re_or_im`.

  COMPATIBILITY NOTE:
  Downstream (e.g. `XiToeplitzRecurrenceIdentity.lean`, `XiWindowLemmaC_FromRecurrence.lean`)
  still expects a semantic lemma named `xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0`.
  We keep that name here as a temporary semantic cliff (separate from jet-nonflatness).
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic
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
  refine Complex.ext ?_ ?_
  · simp [sc, t, anchorScalar, sub_eq_add_neg, Complex.mul_re, Complex.mul_im, pow_two]
    ring_nf
  · simp [sc, t, anchorScalar, sub_eq_add_neg, Complex.mul_re, Complex.mul_im, pow_two]
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

/-- Stable “anchor” statement (kept for documentation / compatibility). -/
def XiAnchorNonvanishing (s : Hyperlocal.OffSeed Xi) : Prop :=
  (completedRiemannZeta (sc s)).re ≠ 0

/-- `XiAnchorNonvanishing` implies the original target `(Xi(sc)).re ≠ 0`. -/
theorem Xi_sc_re_ne_zero_of_anchor (s : Hyperlocal.OffSeed Xi)
    (h : XiAnchorNonvanishing s) : (Xi (sc s)).re ≠ 0 := by
  have ha : (anchorScalar s) ≠ 0 := by
    simpa [anchorScalar] using (anchorScalar_ne_zero (u := t s))
  rw [Xi_sc_re_eq (s := s)]
  exact mul_ne_zero ha h

/-!
LEGACY COMPATIBILITY (temporary):

Some downstream modules still package “Lemma C” at order 0 and therefore
require a value-level nonvanishing assumption for `(Xi (sc s)).re`.

The Option-ELL path is now refactored to avoid using this axiom, but we keep
the name here until the remaining order-0 Lemma-C pipeline is migrated to the
AtOrder payload constructors.
-/
axiom xi_sc_re_ne_zero (s : Hyperlocal.OffSeed Xi) : (Xi (sc s)).re ≠ 0

/-- Stronger form: some order has nonzero real part at the anchor (semantic cliff). -/
theorem xiJetNonflat_re (s : Hyperlocal.OffSeed Xi) :
    ∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0 :=
by
  -- Fully-qualified to avoid name-resolution issues across imports.
  simpa using (_root_.Hyperlocal.Targets.XiPacket.xiJetNonflat_re_exists (s := s))

/-!
## Route B: JetPivot nonflatness at the anchor

The remaining semantic input is imported as `xiJetNonflat_exists`.
We expose it in the local API as `xiJetNonflat` and the Re/Im split form
`xiJetNonflat_re_or_im`.
-/

/-- Semantic nonflatness at the anchor: some complex derivative is nonzero. -/
def XiJetNonflat (s : Hyperlocal.OffSeed Xi) : Prop :=
  ∃ m : ℕ, (cderivIter m Xi) (sc s) ≠ 0

/-- Route-B nonflatness (currently sourced from `XiJetNonflatOfAnalytic`). -/
theorem xiJetNonflat (s : Hyperlocal.OffSeed Xi) : XiJetNonflat s := by
  simpa [XiJetNonflat] using (xiJetNonflat_exists (s := s))

private lemma complex_eq_zero_of_re_im_eq_zero {z : ℂ}
    (hre : z.re = 0) (him : z.im = 0) : z = 0 :=
  Complex.ext hre him

/-- If a complex number is nonzero, then at least one of its real/imag parts is nonzero. -/
lemma re_ne_zero_or_im_ne_zero_of_ne_zero {z : ℂ} (hz : z ≠ 0) : z.re ≠ 0 ∨ z.im ≠ 0 := by
  by_contra h
  have hre : z.re = 0 := by
    exact Classical.byContradiction (fun hre => h (Or.inl hre))
  have him : z.im = 0 := by
    exact Classical.byContradiction (fun him => h (Or.inr him))
  exact hz (complex_eq_zero_of_re_im_eq_zero hre him)

/-- Re/Im split form used by the AtOrder payload constructor layer. -/
theorem xiJetNonflat_re_or_im (s : Hyperlocal.OffSeed Xi) :
    (∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0)
    ∨ (∃ m : ℕ, (((cderivIter m Xi) (sc s))).im ≠ 0) := by
  rcases xiJetNonflat (s := s) with ⟨m, hm⟩
  have hparts :
      ((cderivIter m Xi) (sc s)).re ≠ 0 ∨ ((cderivIter m Xi) (sc s)).im ≠ 0 :=
    re_ne_zero_or_im_ne_zero_of_ne_zero hm
  cases hparts with
  | inl hre => exact Or.inl ⟨m, hre⟩
  | inr him => exact Or.inr ⟨m, him⟩

end XiPacket
end Targets
end Hyperlocal
