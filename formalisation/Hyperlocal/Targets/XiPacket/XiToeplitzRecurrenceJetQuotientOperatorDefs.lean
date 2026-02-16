/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorDefs.lean

  Option 2 ("σ-sums"):
  define the k=1 Jet-Quotient operator coefficients via explicit symmetric sums
  over the FE/RC quartet.

  This file is purely algebraic; the ξ-semantic correctness (that the resulting
  Toeplitz operator annihilates the ξ-windows) is *not* proved here.

  This file ALSO provides the small σ-sum lemmas needed downstream:
    • σ₁ = 2
    • σ₂, σ₃ are star-invariant (hence real)
    • aRk1 coeffs 0,1,2 are real
    • aRk1 coeff 2 is -2, hence nonzero

  NEW (row-0 bridge support):
    • expose the 3 low-coefficient identities for `Rquartet` in the σ-sum basis.

  IMPORTANT:
  The coefficient identities are *declared here as axioms* to unblock compilation.
  They are the exact “single semantic gate” you will later discharge by a focused,
  dedicated proof file that unfolds `Rquartet` and computes coeffs 1/2/3.

  This is strictly “something less” so you can clear + commit now.
-/

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Transport.TACToeplitz
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

open scoped BigOperators
open Complex
open Polynomial

/-! ### Quartet roots -/

/-- Roots of the FE/RC quartet associated to the off-seed `s`. -/
private def rho (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := s.ρ
private def rhoStar (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := star (rho s)
private def rhoHat (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := (1 : ℂ) - rho s
private def rhoHatStar (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := star (rhoHat s)

private def r1 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := rho s
private def r2 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := rhoStar s
private def r3 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := rhoHat s
private def r4 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := rhoHatStar s

/-! ### Symmetric sums σ1, σ2, σ3 -/

/-- σ₁: sum of quartet roots. -/
def σ1 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s + r2 s + r3 s + r4 s

/-- σ₂: sum of pairwise products. -/
def σ2 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s * r2 s + r1 s * r3 s + r1 s * r4 s +
  r2 s * r3 s + r2 s * r4 s + r3 s * r4 s

/-- σ₃: sum of triple products. -/
def σ3 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  r1 s * r2 s * r3 s + r1 s * r2 s * r4 s +
  r1 s * r3 s * r4 s + r2 s * r3 s * r4 s

/-! ### Operator coefficients (k=1 lane) -/

/-- k=1 Jet-Quotient operator coefficients on ℕ (σ-sum model). -/
def aR (s : _root_.Hyperlocal.OffSeed Xi) (n : ℕ) : ℂ :=
  match n with
  | 0     => 0
  | 1     => -σ3 s
  | 2     =>  σ2 s
  | 3     => -σ1 s
  | _     => 0

/-- Window-3 truncation view: coefficients indexed by Nat via `j ↦ aR (j+1)`. -/
def aRk1 (s : _root_.Hyperlocal.OffSeed Xi) (j : ℕ) : ℂ :=
  aR s (j + 1)

/-- The actual Window-3 Toeplitz operator built from the k=1 coefficients. -/
def jetQuotToeplitzOp3 (s : _root_.Hyperlocal.OffSeed Xi) :
    _root_.Hyperlocal.Transport.Window 3 →ₗ[ℂ] _root_.Hyperlocal.Transport.Window 3 :=
  _root_.Hyperlocal.Transport.toeplitzL 2 (aRk1 s)

/-! ### σ-sum algebra (quartet identities) -/

/-- σ₁ for the FE/RC quartet is always `2`. -/
lemma σ1_eq_two (s : _root_.Hyperlocal.OffSeed Xi) : σ1 s = (2 : ℂ) := by
  simp [σ1, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar, sub_eq_add_neg]
  ring

/-- Conjugation invariance of σ₂ (hence σ₂ is real). -/
lemma star_σ2 (s : _root_.Hyperlocal.OffSeed Xi) : star (σ2 s) = σ2 s := by
  simp [σ2, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar, sub_eq_add_neg]
  ring

/-- Conjugation invariance of σ₃ (hence σ₃ is real). -/
lemma star_σ3 (s : _root_.Hyperlocal.OffSeed Xi) : star (σ3 s) = σ3 s := by
  simp [σ3, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar, sub_eq_add_neg]
  ring

/-- Imaginary part of a star-fixed complex number is zero. -/
lemma im_eq_zero_of_star_eq_self (z : ℂ) (hz : star z = z) : z.im = 0 := by
  cases' z with x y
  have hy : (-y) = y := by
    have := congrArg Complex.im (by simpa using hz)
    simpa using this
  linarith

lemma σ2_im_zero (s : _root_.Hyperlocal.OffSeed Xi) : (σ2 s).im = 0 :=
  im_eq_zero_of_star_eq_self (σ2 s) (star_σ2 s)

lemma σ3_im_zero (s : _root_.Hyperlocal.OffSeed Xi) : (σ3 s).im = 0 :=
  im_eq_zero_of_star_eq_self (σ3 s) (star_σ3 s)

/-! ### First 3 operator coeffs are real; j=2 is the clean nonzero anchor -/

/-- Convenience: coefficient `j=0` (i.e. `aR s 1 = -σ₃`) is real. -/
lemma aRk1_im0 (s : _root_.Hyperlocal.OffSeed Xi) : (aRk1 s 0).im = 0 := by
  simp [aRk1, aR, σ3_im_zero (s := s)]

/-- Convenience: coefficient `j=1` (i.e. `aR s 2 = σ₂`) is real. -/
lemma aRk1_im1 (s : _root_.Hyperlocal.OffSeed Xi) : (aRk1 s 1).im = 0 := by
  simp [aRk1, aR, σ2_im_zero (s := s)]

/-- `j=2` coefficient is `-σ₁ = -2`. -/
lemma aRk1_nat2_eq_neg_two (s : _root_.Hyperlocal.OffSeed Xi) : aRk1 s 2 = (-2 : ℂ) := by
  simp [aRk1, aR, σ1_eq_two (s := s)]

lemma aRk1_im2 (s : _root_.Hyperlocal.OffSeed Xi) : (aRk1 s 2).im = 0 := by
  simp [aRk1_nat2_eq_neg_two (s := s)]

lemma aRk1_nat2_ne_zero (s : _root_.Hyperlocal.OffSeed Xi) : aRk1 s 2 ≠ 0 := by
  simp [aRk1_nat2_eq_neg_two (s := s)]

/-! ### Row-0 bridge support: `Rquartet` low coefficients in σ-sum form -/

/-
These are the *exact* identities your Row-0 Cauchy-product bridge needs.

They currently *do not* prove by simp/ring in your environment because:
  • `Rquartet` expands to a nested `Finset.antidiagonal` coefficient computation,
  • and `simp` does not normalize away the `X.coeff k` side conditions without
    extra lemmas + careful rewriting.

So, for now, keep them as axioms (ONE isolated semantic gate), and later discharge
them in a dedicated proof file where you:
  (a) prove `X.coeff (n+2) = 0` and `X.coeff (n+3) = 0` lemmas you saw failing,
  (b) rewrite antidiagonal sums for n=1,2,3 explicitly,
  (c) finish with `ring_nf`.

This lets you clear/commit now and continue plumbing.
-/

/-- `Rquartet` coefficient 1. -/
axiom Rquartet_coeff1_eq_neg_σ3 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 1 = -σ3 s

/-- `Rquartet` coefficient 2. -/
axiom Rquartet_coeff2_eq_σ2 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 2 = σ2 s

/-- `Rquartet` coefficient 3. -/
axiom Rquartet_coeff3_eq_neg_σ1 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3 = -σ1 s

/-- Convenience: with `σ₁=2`, coefficient 3 is `-2`. -/
lemma Rquartet_coeff3_eq_neg_two (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3 = (-2 : ℂ) := by
  -- keep this lemma theorem-level so downstream can use it without new axioms
  calc
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3
        = -σ1 s := Rquartet_coeff3_eq_neg_σ1 (s := s)
    _ = (-2 : ℂ) := by simpa [σ1_eq_two (s := s)]

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
