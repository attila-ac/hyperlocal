/-
FILE (complete replacement):
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorCoeffs.lean

Purpose:
  Discharge the three `Rquartet.coeff` identities as THEOREMS (degrees 1/2/3 only),
  via a compact Vieta normal form + coefficient extraction.

Key fix vs your current attempt:
  * Do NOT try to rewrite the `Rquartet` roots to `JetQuotOp.r1/r2/r3/r4` inside the Vieta proof.
    `Rquartet` (from XiAnalyticInputs) uses its *own* local root binders (hence the `r1✝` etc),
    and unfolding to your `r1` causes mismatches.
  * Instead: build a *local* σ₁/σ₂/σ₃ (`σ1' σ2' σ3'`) directly from the same root expressions
    that appear in `Rquartet` (namely `s.ρ`, `starRingEnd ℂ s.ρ`, `1 - s.ρ`, `1 - starRingEnd ℂ s.ρ`).
    Then prove `σi' = σi` by simp.

Important:
  If you still see “has already been declared”, then there is still another declaration of these
  theorems in your build graph. Search and delete/rename the duplicate source:
    grep -R "theorem Rquartet_coeff1_eq_neg_σ3" -n formalisation/Hyperlocal
  Then rebuild.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

open Polynomial

/-! ### Root expressions matching `Rquartet` (do NOT use `JetQuotOp.r1` here) -/

private def rq1 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := s.ρ
private def rq2 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ
private def rq3 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := (1 : ℂ) - s.ρ
private def rq4 (s : _root_.Hyperlocal.OffSeed Xi) : ℂ := (1 : ℂ) - (starRingEnd ℂ) s.ρ

private def σ1' (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  rq1 s + rq2 s + rq3 s + rq4 s

private def σ2' (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  rq1 s * rq2 s + rq1 s * rq3 s + rq1 s * rq4 s +
  rq2 s * rq3 s + rq2 s * rq4 s + rq3 s * rq4 s

private def σ3' (s : _root_.Hyperlocal.OffSeed Xi) : ℂ :=
  rq1 s * rq2 s * rq3 s + rq1 s * rq2 s * rq4 s +
  rq1 s * rq3 s * rq4 s + rq2 s * rq3 s * rq4 s

private lemma σ1'_eq_σ1 (s : _root_.Hyperlocal.OffSeed Xi) : σ1' s = σ1 s := by
  simp [σ1', σ1, rq1, rq2, rq3, rq4, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar]

private lemma σ2'_eq_σ2 (s : _root_.Hyperlocal.OffSeed Xi) : σ2' s = σ2 s := by
  simp [σ2', σ2, rq1, rq2, rq3, rq4, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar]

private lemma σ3'_eq_σ3 (s : _root_.Hyperlocal.OffSeed Xi) : σ3' s = σ3 s := by
  simp [σ3', σ3, rq1, rq2, rq3, rq4, r1, r2, r3, r4, rho, rhoStar, rhoHat, rhoHatStar]

/-! ### Vieta normal form for `Rquartet` (σ'-version) -/

private lemma Rquartet_vieta' (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ)
      =
        (X : Polynomial ℂ)^4
        - (C (σ1' s)) * (X : Polynomial ℂ)^3
        + (C (σ2' s)) * (X : Polynomial ℂ)^2
        - (C (σ3' s)) * (X : Polynomial ℂ)
        + C (rq1 s * rq2 s * rq3 s * rq4 s) := by
  classical
  -- Expand the product-of-linear-factors definition of `Rquartet` and normalize.
  -- This stays aligned with `Rquartet`'s internal root expressions.
  simp [_root_.Hyperlocal.Targets.XiPacket.Rquartet,
        σ1', σ2', σ3', rq1, rq2, rq3, rq4, sub_eq_add_neg]
  ring_nf

/-! ### Coefficient identities (degrees 1/2/3 only) -/

theorem Rquartet_coeff1_eq_neg_σ3 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 1 = -σ3 s := by
  classical
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 1) (Rquartet_vieta' (s := s))
  -- only the `-(C (σ3' s)) * X` term contributes at degree 1
  have : (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 1 = -σ3' s := by
    simpa using h
  simpa [σ3'_eq_σ3 (s := s)] using this

theorem Rquartet_coeff2_eq_σ2 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 2 = σ2 s := by
  classical
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 2) (Rquartet_vieta' (s := s))
  -- only the `(C (σ2' s)) * X^2` term contributes at degree 2
  have : (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 2 = σ2' s := by
    simpa using h
  simpa [σ2'_eq_σ2 (s := s)] using this

theorem Rquartet_coeff3_eq_neg_σ1 (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3 = -σ1 s := by
  classical
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 3) (Rquartet_vieta' (s := s))
  -- only the `-(C (σ1' s)) * X^3` term contributes at degree 3
  have : (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3 = -σ1' s := by
    simpa using h
  simpa [σ1'_eq_σ1 (s := s)] using this

theorem Rquartet_coeff3_eq_neg_two (s : _root_.Hyperlocal.OffSeed Xi) :
    (_root_.Hyperlocal.Targets.XiPacket.Rquartet s.ρ).coeff 3 = (-2 : ℂ) := by
  simpa [σ1_eq_two (s := s)] using (Rquartet_coeff3_eq_neg_σ1 (s := s))

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
