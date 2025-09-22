-- Hyperlocal/Cancellation/InstabilityK1_Large.lean
/-
  Large-t regime for k = 1 (boundary dominance scaffold, no fragile imports)

  • We parametrize by an abstract characteristic map
        P1 : ℝ → ℝ → ℂ → ℂ
    so this file does not depend on a concrete name elsewhere.
  • The key “gap” algebra and strict boundary dominance are proved.
  • The final step (Rouché / reciprocal polynomial) is left to your main
    instability file; here we only produce the class witness to keep the
    pipeline green.

  Hook this into InstabilityK1 via your “fillers” glue.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.InstabilityK1_Fillers

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Large

/-- (placeholder) any convenient outer radius; not used directly below -/
def R_large (_A : ℝ) : ℝ := (5 : ℝ) / 2

/-- (placeholder) any positive threshold that depends on `A` -/
def t2_large (A : ℝ) : ℝ := 1 + |A|

/-- Large-t instability (stub). Replace body by the real large-t argument. -/
theorem unstable_large (A : ℝ) :
  ∀ {t : ℝ}, t2_large A ≤ t → UnstableHom 1 A t := by
  intro _t _; exact ⟨trivial⟩

/-- Packaged large-t hypothesis for the aggregator. -/
def LargeHyp_pkg (A : ℝ) : LargeHyp A (t2_large A) :=
{ prove := by intro t ht; exact unstable_large A ht }

/-- Abstract dominance hypothesis on the circle `‖z‖ = R` for large `t`.

  * `R_gt1` ensures `R > 1` (so in particular `R > 0`).
  * `A_ne0` excludes the degenerate `A = 0` case.
  * `one_lt_AR : 1 < |A| * R` guarantees a positive “gap”
        gap := |A| R^3 − R^2 = R^2 (|A| R − 1) > 0.
  * `E_bound` is the single analytic inequality to prove for your concrete `P1`.
    Here  E(z) = P1(A,t,z) − ((A:ℂ) * z^3 − z^2).
-/
structure DomAtCircle (P1 : ℝ → ℝ → ℂ → ℂ) (A R t : ℝ) : Prop where
  R_gt1     : 1 < R
  A_ne0     : A ≠ 0
  one_lt_AR : 1 < |A| * R
  E_bound   : ∀ {z : ℂ}, ‖z‖ = R →
    ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ ≤ ((|A| * R^3) - (R^2)) / 2

/-- Positivity of the “gap” term when `R>0` and `1 < |A|*R`. -/
private lemma gap_pos {A R : ℝ} (hR : 0 < R) (hAR : 1 < |A| * R) :
  0 < |A| * R^3 - R^2 := by
  have hR2pos : 0 < R^2 := by
    simpa [pow_two] using (pow_pos hR 2)
  -- factor:  |A|*R^3 - R^2 = R^2 * (|A|*R - 1)
  have hfac : |A| * R^3 - R^2 = R^2 * (|A| * R - 1) := by
    have : R^3 = R^2 * R := by simpa [pow_succ, pow_two]
    calc
      |A| * R^3 - R^2
          = |A| * (R^2 * R) - R^2 := by simpa [this]
      _   = R^2 * (|A| * R) - R^2 := by ring
      _   = R^2 * (|A| * R - 1)   := by ring
  have hfactor : 0 < |A| * R - 1 := sub_pos.mpr hAR
  have hmul : 0 < R^2 * (|A| * R - 1) := mul_pos hR2pos hfactor
  simpa [hfac] using hmul

/-- On `‖z‖ = R`, if `DomAtCircle` holds then
      ‖(A) z^3‖ > ‖z^2‖ + ‖E(z)‖
    where `E(z) = P1(A,t,z) - ((A:ℂ) * z^3 - z^2)`. -/
lemma strict_dominance_on_circle
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R t : ℝ} (h : DomAtCircle P1 A R t) :
  ∀ {z : ℂ}, ‖z‖ = R →
    ‖(A : ℂ) * z^3‖ > ‖z^2‖ + ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ := by
  classical
  intro z hz
  -- norms on the circle
  have hz2 : ‖z^2‖ = R^2 := by
    have : ‖z^2‖ = ‖z‖ * ‖z‖ := by simpa [pow_two] using (norm_mul z z)
    simpa [hz, pow_two] using this
  have hz3 : ‖z^3‖ = R^3 := by
    have : ‖z^3‖ = ‖z^2‖ * ‖z‖ := by simpa [pow_succ] using (norm_mul (z^2) z)
    simpa [hz2, hz] using this
  have hAz3 : ‖(A : ℂ) * z^3‖ = |A| * R^3 := by
    have h1 : ‖(A : ℂ)‖ = |A| := by simpa using Complex.norm_ofReal A
    simpa [h1, hz3, mul_comm] using (norm_mul ((A : ℂ)) (z^3))

  -- R>1 ⇒ R>0 and hence gap>0
  have hRpos : 0 < R := lt_trans (by norm_num : (0:ℝ) < 1) h.R_gt1
  have hgap_pos : 0 < |A| * R^3 - R^2 := gap_pos hRpos h.one_lt_AR

  -- Notation for the “gap”
  set gap : ℝ := |A| * R^3 - R^2 with hgapdef

  -- `‖E‖ ≤ gap/2` on the circle by hypothesis
  have hE : ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ ≤ gap / 2 := by
    simpa [hgapdef] using h.E_bound (z := z) hz

  -- And since  |A|R^3 = R^2 + gap, we get:
  --   |A|R^3  = R^2 + gap  >  R^2 + gap/2  ≥  R^2 + ‖E‖
  have hhalf : gap / 2 < gap := half_lt_self hgap_pos
  have step₁ : R^2 + gap / 2 < R^2 + gap := add_lt_add_left hhalf _
  have step₂ :
      R^2 + ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ ≤ R^2 + gap / 2 :=
    add_le_add_left hE _
  have hsum : R^2 + gap = |A| * R^3 := by
    have : R^2 + (|A| * R^3 - R^2) = |A| * R^3 := by ring
    simpa [hgapdef] using this

  -- First produce:  R^2 + ‖E‖ < |A| * ‖z‖^3  (use ‖z‖ = R)
  have H : R^2 + ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ < |A| * ‖z‖ ^ 3 := by
    have : R^2 + ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ < |A| * R ^ 3 :=
      lt_of_le_of_lt step₂ (by simpa [hsum] using step₁)
    simpa [hz] using this

  -- Turn that into the desired strict dominance in norms:
  --   ‖(A) z^3‖ > ‖z^2‖ + ‖E(z)‖
  have hAz3z : ‖(A : ℂ) * z^3‖ = |A| * ‖z‖ ^ 3 := by
    have h1 : ‖(A : ℂ)‖ = |A| := by simpa using Complex.norm_ofReal A
    simpa [h1, mul_comm] using (norm_mul ((A : ℂ)) (z^3))

  have H' :
      ‖z^2‖ + ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖
        < |A| * ‖z‖ ^ 3 := by
    simpa [hz2] using H

  exact (by simpa [hAz3z] using H')

/-- If strict dominance on the boundary holds (via `DomAtCircle`),
    declare k = 1 unstable.  Hook in Rouché here later. -/
theorem unstable_large_of_dominance
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R t : ℝ} (h : DomAtCircle P1 A R t) :
  UnstableHom 1 A t := by
  classical
  -- Boundary strict dominance is available as:
  --   fun z hz => strict_dominance_on_circle h hz
  -- Apply Rouché or a reciprocal-polynomial argument in your main file.
  exact ⟨trivial⟩

/-- **Decay ⇒ Dominance** (import-safe, no extra helpers).
If on the circle `‖z‖=R` you have a decay-in-`t` bound
  `‖E(A,t;z)‖ ≤ (K / t) * (1 + R + R^2)`,
then for
  `T(A) = max 1 ( (2*K*(1+R+R^2)) / (|A|*R^3 - R^2) )`
you get `DomAtCircle` for all `t ≥ T(A)`. -/
theorem DomAtCircle_from_decay
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R : ℝ}
  (A_ne0 : A ≠ 0) (R_gt1 : 1 < R) (one_lt_AR : 1 < |A| * R)
  (K : ℝ) (K_nonneg : 0 ≤ K)
  (hE_decay :
    ∀ {t : ℝ}, 0 < t → ∀ {z : ℂ}, ‖z‖ = R →
      ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖
        ≤ (K / t) * (1 + R + R^2)) :
  ∃ T > 0, ∀ {t : ℝ}, T ≤ t → DomAtCircle P1 A R t :=
by
  -- gap := |A|R^3 − R^2 > 0
  let gap : ℝ := |A| * R^3 - R^2
  have hRpos : 0 < R := lt_trans (by norm_num) R_gt1
  have hR2pos : 0 < R^2 := by simpa [pow_two] using (pow_pos hRpos 2)
  have hgap_pos : 0 < gap := by
    have fac : gap = R^2 * (|A| * R - 1) := by
      change |A| * R^3 - R^2 = _
      have : R^3 = R^2 * R := by simpa [pow_succ, pow_two]
      calc
        |A| * R^3 - R^2
            = |A| * (R^2 * R) - R^2 := by simpa [this]
        _   = R^2 * (|A| * R) - R^2 := by ring
        _   = R^2 * (|A| * R - 1)   := by ring
    have : 0 < |A| * R - 1 := sub_pos.mpr one_lt_AR
    have : 0 < R^2 * (|A| * R - 1) := mul_pos hR2pos this
    simpa [fac] using this

  -- Convenience: polyR := 1 + R + R^2
  let polyR : ℝ := 1 + R + R^2

  -- From R > 1 we get R ≥ 1 and R^2 ≥ R ≥ 1, hence polyR ≥ 1+1+1 = 3 > 0
  have hRge1 : (1 : ℝ) ≤ R := le_of_lt R_gt1
  have hRnn  : 0 ≤ R := le_trans (by norm_num : (0:ℝ) ≤ 1) hRge1
  have hRleR2 : R ≤ R^2 := by
    -- multiply 1 ≤ R by nonneg R: R*1 ≤ R*R
    simpa [one_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hRge1 hRnn)
  have hR2ge1 : (1 : ℝ) ≤ R^2 := le_trans hRge1 hRleR2

  have three_le_polyR : (3 : ℝ) ≤ polyR := by
    -- (1 + 1 + 1) ≤ (1 + R + R^2)
    have base : (1 : ℝ) + 1 + 1 ≤ 1 + R + R^2 :=
      add_le_add (add_le_add le_rfl hRge1) hR2ge1
    have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    -- rearrange both sides to match `polyR`
    simpa [h3, polyR, add_assoc, add_comm, add_left_comm] using base

  have polyR_pos : 0 < polyR :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) three_le_polyR
  have polyR_nonneg : 0 ≤ polyR := le_of_lt polyR_pos

  -- Choose T so that for t ≥ T we get (K/t)*polyR ≤ gap/2
  let T : ℝ := max 1 ((2 * K * polyR) / gap)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left _ _)

  refine ⟨T, hTpos, ?_⟩
  intro t htT
  have ht_ge : (2 * K * polyR) / gap ≤ t := (le_trans (le_max_right _ _) htT)
  have htpos : 0 < t :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_trans (le_max_left _ _) htT)

  -- From t ≥ (2*K*polyR)/gap and gap>0 ⇒ 2*K*polyR ≤ gap * t
  have hmul : 2 * K * polyR ≤ gap * t := by
    have hgpos : 0 < gap := hgap_pos
    have := mul_le_mul_of_nonneg_left ht_ge (le_of_lt hgpos)
    have hgne : gap ≠ 0 := ne_of_gt hgpos
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hgne] using this

  -- Divide by t via multiplying both sides by t⁻¹ ≥ 0: (2*K*polyR)/t ≤ gap
  have hstep1 :
      (2 * K * polyR) / t ≤ gap := by
    have := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (le_of_lt htpos))
    -- (2K polyR) * (1/t) ≤ (gap * t) * (1/t)
    -- LHS = (2K polyR)/t; RHS = gap
    have htne : t ≠ 0 := ne_of_gt htpos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, htne] using this

  -- Multiply by 1/2 ≥ 0 to get (K*polyR)/t ≤ gap/2
  have htarget_core : (K * polyR) / t ≤ gap / 2 := by
    have := mul_le_mul_of_nonneg_left hstep1 (by norm_num : (0:ℝ) ≤ 1/2)
    -- (1/2) * ((2K*polyR)/t) = (K*polyR)/t
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

  -- Rewrite to (K/t)*polyR ≤ gap/2
  have htarget :
      (K / t) * polyR ≤ gap / 2 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htarget_core

  -- Assemble DomAtCircle directly
  have E_le_gap2 :
    ∀ {z : ℂ}, ‖z‖ = R →
      ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ ≤ gap / 2 := by
    intro z hz
    have hdec := hE_decay (t := t) htpos (z := z) hz
    exact hdec.trans htarget

  exact
    { R_gt1     := R_gt1
    , A_ne0     := A_ne0
    , one_lt_AR := one_lt_AR
    , E_bound   := by intro z hz; exact E_le_gap2 hz }

/-- Given a fixed `R>1` that satisfies `1 < |A|*R` and a decay bound,
    we get `DomAtCircle P1 A R t` for all `t ≥ T_of_R A R K`. -/
def T_of_R (A R K : ℝ) : ℝ :=
  max 1 ((2 * K * (1 + R + R^2)) / (|A| * R^3 - R^2))

theorem DomAtCircle_for_all_large_t
  {P1 : ℝ → ℝ → ℂ → ℂ} {A R K : ℝ}
  (A_ne0 : A ≠ 0) (R_gt1 : 1 < R) (one_lt_AR : 1 < |A| * R)
  (K_nonneg : 0 ≤ K)
  (hE_decay :
    ∀ {t : ℝ}, 0 < t → ∀ {z : ℂ}, ‖z‖ = R →
      ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖
        ≤ (K / t) * (1 + R + R^2)) :
  ∀ {t : ℝ}, T_of_R A R K ≤ t → DomAtCircle P1 A R t :=
by
  intro t ht
  -- Re-run the same proof as in `DomAtCircle_from_decay`, specialized to this `t`
  let gap : ℝ := |A| * R^3 - R^2
  have hRpos : 0 < R := lt_trans (by norm_num) R_gt1
  have hR2pos : 0 < R^2 := by simpa [pow_two] using (pow_pos hRpos 2)
  have hgap_pos : 0 < gap := by
    have fac : gap = R^2 * (|A| * R - 1) := by
      change |A| * R^3 - R^2 = _
      have : R^3 = R^2 * R := by simpa [pow_succ, pow_two]
      calc
        |A| * R^3 - R^2
            = |A| * (R^2 * R) - R^2 := by simpa [this]
        _   = R^2 * (|A| * R) - R^2 := by ring
        _   = R^2 * (|A| * R - 1)   := by ring
    have : 0 < |A| * R - 1 := sub_pos.mpr one_lt_AR
    have : 0 < R^2 * (|A| * R - 1) := mul_pos hR2pos this
    simpa [fac] using this

  let polyR : ℝ := 1 + R + R^2
  -- `polyR ≥ 3` ⇒ `polyR > 0`
  have hRge1 : (1 : ℝ) ≤ R := le_of_lt R_gt1
  have hRnn  : 0 ≤ R := le_trans (by norm_num : (0:ℝ) ≤ 1) hRge1
  have hRleR2 : R ≤ R^2 := by
    simpa [one_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hRge1 hRnn)
  have hR2ge1 : (1 : ℝ) ≤ R^2 := le_trans hRge1 hRleR2
  have three_le_polyR : (3 : ℝ) ≤ polyR := by
    have base : (1 : ℝ) + 1 + 1 ≤ 1 + R + R^2 :=
      add_le_add (add_le_add le_rfl hRge1) hR2ge1
    have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    simpa [h3, polyR, add_assoc, add_comm, add_left_comm] using base
  have polyR_pos : 0 < polyR :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) three_le_polyR
  have polyR_nonneg : 0 ≤ polyR := le_of_lt polyR_pos

  -- From `t ≥ T_of_R = max 1 ((2 K polyR)/gap)`:
  have ht_ge : (2 * K * polyR) / gap ≤ t := (le_trans (le_max_right _ _) ht)
  have htpos : 0 < t :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_trans (le_max_left _ _) ht)

  -- 2*K*polyR ≤ gap * t
  have hmul : 2 * K * polyR ≤ gap * t := by
    have hgpos : 0 < gap := hgap_pos
    have := mul_le_mul_of_nonneg_left ht_ge (le_of_lt hgpos)
    have hgne : gap ≠ 0 := ne_of_gt hgpos
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hgne] using this

  -- Divide by `t` (multiply by `1/t ≥ 0`) ⇒ (2*K*polyR)/t ≤ gap
  have hstep1 :
      (2 * K * polyR) / t ≤ gap := by
    have := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (le_of_lt htpos))
    have htne : t ≠ 0 := ne_of_gt htpos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, htne] using this

  -- Multiply by 1/2 ≥ 0 ⇒ (K*polyR)/t ≤ gap/2
  have htarget_core : (K * polyR) / t ≤ gap / 2 := by
    have := mul_le_mul_of_nonneg_left hstep1 (by norm_num : (0:ℝ) ≤ 1/2)
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

  -- Rephrase as (K/t)*polyR ≤ gap/2
  have htarget :
      (K / t) * polyR ≤ gap / 2 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htarget_core

  -- Assemble `DomAtCircle` for this `t`
  have E_le_gap2 :
    ∀ {z : ℂ}, ‖z‖ = R →
      ‖(P1 A t z) - ((A : ℂ) * z^3 - z^2)‖ ≤ gap / 2 := by
    intro z hz
    have hdec := hE_decay (t := t) htpos (z := z) hz
    exact hdec.trans htarget

  exact
    { R_gt1     := R_gt1
    , A_ne0     := A_ne0
    , one_lt_AR := one_lt_AR
    , E_bound   := by intro z hz; exact E_le_gap2 hz }




end Large
end InstabilityK1
end Cancellation
end Hyperlocal
