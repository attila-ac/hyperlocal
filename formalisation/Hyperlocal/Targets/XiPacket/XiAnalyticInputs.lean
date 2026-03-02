/-
  Hyperlocal/Targets/XiPacket/XiAnalyticInputs.lean

  Cancellation shim + Xi_entire closure adjusted.

  Snapshot reality:
  * This Mathlib snapshot does not expose a usable “mellin commutes with conj/starRingEnd”
    lemma under any stable name (your grep confirms this).
  * Therefore we implement the missing lemma locally (axiom-free) and discharge the RC hinge.

  Everything (analyticity, RC, cancellation shim, Xi_entire, quartet polynomial facts) is theorem-level.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Core
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.MinimalModel
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.GrowthOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial
open scoped Topology
open scoped BigOperators
open scoped ComplexConjugate
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization
open MeasureTheory

private abbrev XiFn : ℂ → ℂ := Hyperlocal.xi
private abbrev conjEnd : ℂ →+* ℂ := starRingEnd ℂ
private def a0 : UnitAddCircle := (0 : UnitAddCircle)

-- ------------------------------------------------------------------
-- Differentiable → AnalyticAt bridge (snapshot-specific helper)
-- ------------------------------------------------------------------

private lemma eventually_of_forall'
    {α : Type} {l : Filter α} {P : α → Prop} (h : ∀ x, P x) :
    (∀ᶠ x in l, P x) := by
  have htrue : (∀ᶠ x in l, True) := by simp
  have hset : ({x : α | P x} : Set α) = {x : α | True} := by
    ext x; simp [h x]
  simpa [Filter.Eventually, hset] using htrue

/-- Λ₀ is analytic everywhere (theorem-level) in this snapshot. -/
theorem completedRiemannZeta₀_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedRiemannZeta₀ z := by
  have hdiff_all : ∀ w : ℂ, DifferentiableAt ℂ completedRiemannZeta₀ w := by
    intro w
    simpa using (differentiable_completedZeta₀.differentiableAt)
  have hev : ∀ᶠ w in nhds z, DifferentiableAt ℂ completedRiemannZeta₀ w :=
    eventually_of_forall' (l := nhds z) hdiff_all
  exact (analyticAt_iff_eventually_differentiableAt).2 hev

-- ------------------------------------------------------------------
-- Reality condition (RC) for Λ₀: axiom-free (Mellin/integral level)
-- ------------------------------------------------------------------

/-- `conj` commutes with restricted integrals over `Ioi 0`. -/
private lemma conj_setIntegral_Ioi0 (g : ℝ → ℂ) :
    conj (∫ (t : ℝ) in Set.Ioi 0, g t) =
      ∫ (t : ℝ) in Set.Ioi 0, conj (g t) := by
  simpa using
    (integral_conj (μ := (volume.restrict (Set.Ioi 0))) (f := g)).symm

/-- `0 ≠ π` in the direction that appears after rewriting `arg = 0`. -/
private lemma zero_ne_pi : (0 : ℝ) ≠ Real.pi := by
  exact ne_of_lt Real.pi_pos

/--
Key snapshot trick:

`conj_cpow` has shape `conj x ^ n = conj (x ^ conj n)` (under `x.arg ≠ π`).
So to rewrite `conj ((↑t)^z)` we *apply it with exponent `conj z`* and then `symm`.

Result:
`conj ((↑t : ℂ) ^ z) = (↑t : ℂ) ^ (conj z)` for `t>0`.
-/
private lemma conj_cpow_ofReal_pos {t : ℝ} (ht : 0 < t) (z : ℂ) :
    conj ((↑t : ℂ) ^ z) = (↑t : ℂ) ^ (conj z) := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have harg0 : ((↑t : ℂ)).arg = 0 := by
    simpa using Complex.arg_ofReal_of_nonneg ht0
  have harg : ((↑t : ℂ)).arg ≠ Real.pi := by
    -- cover both `0 ≠ π` and `¬ 0 = π` shapes
    simpa [harg0, eq_comm] using zero_ne_pi
  -- use exponent `conj z` so RHS becomes `conj ((↑t)^z)`
  have h := (Complex.conj_cpow (↑t : ℂ) (conj z) harg)
  -- h : conj (↑t) ^ conj z = conj ((↑t) ^ conj (conj z))
  -- simp: conj (↑t)=↑t and conj (conj z)=z, then `symm`
  simpa using h.symm

/--
Mellin conjugation hinge (axiom-free, snapshot-robust):

`mellin f (conj s) = conj (mellin (fun t => conj (f t)) s)`.

We *do not* try to use any missing `integral_star` / `conj_add` / `conj_sub` lemmas.
We only use:
* `integral_conj` (via `conj_setIntegral_Ioi0`)
* the cpow trick `conj_cpow_ofReal_pos`
* pointwise `simp` + commutativity.
-/
private lemma mellin_conj (f : ℝ → ℂ) (s : ℂ) :
    mellin f (conj s) = conj (mellin (fun t => conj (f t)) s) := by
  classical
  -- unfold to the exact setIntegral shape used in this snapshot
  simp [mellin, sub_eq_add_neg, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  -- goal is now a setIntegral equality; rewrite RHS `conj (∫ ...)` using `integral_conj`
  have hpush :
      conj (∫ (t : ℝ) in Set.Ioi 0, (↑t : ℂ) ^ (s + (-1 : ℂ)) * conj (f t)) =
        ∫ (t : ℝ) in Set.Ioi 0, conj ((↑t : ℂ) ^ (s + (-1 : ℂ)) * conj (f t)) := by
    simpa using (conj_setIntegral_Ioi0 (g := fun t =>
      (↑t : ℂ) ^ (s + (-1 : ℂ)) * conj (f t)))
  -- after `simp` above, the RHS really is `conj (∫ ...)`
  rw [hpush]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have htpos : 0 < t := ht
  have hexp : conj (s + (-1 : ℂ)) = conj s + (-1 : ℂ) := by simp
  -- compute `conj (t^(s-1) * conj(f t))`
  -- the only nontrivial rewrite is `conj (t^z)` via the cpow trick
  -- then commutativity aligns the factors with the unfolded Mellin LHS.
  simp [hexp, conj_mul, mul_assoc, mul_left_comm, mul_comm,
        conj_cpow_ofReal_pos (t := t) htpos (z := (s + (-1 : ℂ)))]

private lemma mellin_conj_of_fixed
    (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  simpa [hf] using (mellin_conj (f := f) (s := s))

/-- Tiny scalar normalization: `(starRingEnd ℂ) 2 = 2`. -/
private lemma starRingEnd_two : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
  simpa using (map_natCast (starRingEnd ℂ) 2)

/-- Reality condition (RC) for `completedRiemannZeta₀` (Λ₀), axiom-free. -/
theorem completedRiemannZeta₀_RC (s : ℂ) :
    completedRiemannZeta₀ (conjEnd s) =
      conjEnd (completedRiemannZeta₀ s) := by
  classical
  dsimp [conjEnd]
  let P : WeakFEPair ℂ := HurwitzZeta.hurwitzEvenFEPair a0

  -- Prove `P.f_modif` is fixed by conjugation, **without** `conj_add/conj_sub`.
  -- We just split indicator membership and let simp handle `conj` on reals.
  have hf : ∀ t : ℝ, conj (P.f_modif t) = P.f_modif t := by
    intro t
    dsimp [P, HurwitzZeta.hurwitzEvenFEPair, WeakFEPair.f_modif, WeakFEPair.g_modif]
    by_cases hIoi : t ∈ Set.Ioi (1 : ℝ)
    · have hIoo : t ∉ Set.Ioo (0 : ℝ) (1 : ℝ) := by
        intro ht01
        -- ht01.2 : t < 1 contradicts 1 < t
        exact (not_lt_of_ge (le_of_lt hIoi)) ht01.2
      -- first indicator is active, second is zero
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hIoi, hIoo, Complex.conj_ofReal]
    · by_cases hIoo : t ∈ Set.Ioo (0 : ℝ) (1 : ℝ)
      · -- second indicator active, first zero
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hIoi, hIoo, Complex.conj_ofReal]
      · -- both indicators zero
        simp [Set.indicator_of_not_mem, hIoi, hIoo]

  -- Apply Mellin hinge at `s/2`.
  have hM : mellin P.f_modif (conj (s / 2)) = conj (mellin P.f_modif (s / 2)) :=
    mellin_conj_of_fixed (f := P.f_modif) hf (s := (s / 2))

  -- Unfold `completedRiemannZeta₀` just enough to expose the Mellin, rewrite with `hM`.
  simp [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀,
        HurwitzZeta.completedHurwitzZetaEven, P, WeakFEPair.Λ₀,
        div_eq_mul_inv, starRingEnd_two] at hM ⊢
  simpa using hM

-- ------------------------------------------------------------------
-- RC for completedRiemannZeta, derived from Λ₀ RC
-- ------------------------------------------------------------------

theorem completedRiemannZeta_RC (s : ℂ) :
    completedRiemannZeta (conjEnd s) =
      conjEnd (completedRiemannZeta s) := by
  classical
  rw [completedRiemannZeta_eq (s := (conjEnd s))]
  rw [completedRiemannZeta_eq (s := s)]
  simp [completedRiemannZeta₀_RC, conjEnd, div_eq_mul_inv,
    sub_eq_add_neg, mul_assoc, add_assoc, add_left_comm, add_comm,
    starRingEnd_two]

-- ------------------------------------------------------------------
-- Cancellation shim (THEOREM-LEVEL): entire extension via Λ₀
-- ------------------------------------------------------------------

/--
Entire extension of the pole-cancelled product.

Normalized form: `w*(w-1)*Λ₀(w) + 1`.
(This is definitional-equal to `w*(w-1)*Λ(w)` on `w ≠ 0,1`.)
-/
def cancelledCompletedZeta (w : ℂ) : ℂ :=
  w * (w - (1 : ℂ)) * completedRiemannZeta₀ w + 1

theorem cancelledCompletedZeta_analyticAt (z : ℂ) :
    AnalyticAt ℂ cancelledCompletedZeta z := by
  have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hconst1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
  have hsub1 : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z := by
    simpa [sub_eq_add_neg] using hid.sub hconst1
  have hΛ0 : AnalyticAt ℂ completedRiemannZeta₀ z :=
    completedRiemannZeta₀_analyticAt (z := z)
  have htermA :
      AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta₀ w) z :=
    (hid.mul hsub1).mul hΛ0
  simpa [cancelledCompletedZeta] using htermA.add analyticAt_const

/--
Valid cancellation on the punctured domain: for `w ≠ 0,1`,
`w*(w-1)*Λ(w) = w*(w-1)*Λ₀(w) + 1`.
-/
theorem cancelledCompletedZeta_eq_raw {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    w * (w - (1 : ℂ)) * completedRiemannZeta w = cancelledCompletedZeta w := by
  classical
  have h1' : (1 - w) ≠ 0 := by
    intro hw
    have hw' : w = 1 := by
      simpa [eq_comm] using (sub_eq_zero.mp hw)
    exact h1 hw'
  simp [cancelledCompletedZeta, completedRiemannZeta_eq (s := w),
    div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] at *
  field_simp [h0, h1, h1']
  ring

-- ------------------------------------------------------------------
-- FE / RC / Entirety for Xi
-- ------------------------------------------------------------------

theorem Xi_FE : Factorization.FunFE XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi, Hyperlocal.oneMinus]
  rw [completedRiemannZeta₀_one_sub (s := s)]
  ring

theorem Xi_RC : FactorizationRC.FunRC XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  simp [conjEnd, completedRiemannZeta₀_RC, mul_assoc, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]

theorem Xi_entire : GrowthOrder.EntireFun XiFn := by
  intro z
  have hz : AnalyticAt ℂ cancelledCompletedZeta z :=
    cancelledCompletedZeta_analyticAt (z := z)
  simpa [XiFn, Hyperlocal.xi, cancelledCompletedZeta] using hz

-- ------------------------------------------------------------------
-- Quartet polynomial (unchanged)
-- ------------------------------------------------------------------

def Rquartet (ρ : ℂ) : Polynomial ℂ :=
  (X - C ρ) *
  (X - C (star ρ)) *
  (X - C (1 - ρ)) *
  (X - C (1 - star ρ))

lemma Rquartet_eval_rho (ρ : ℂ) :
    (Rquartet ρ).eval ρ = 0 := by simp [Rquartet]

lemma Rquartet_eval_star (ρ : ℂ) :
    (Rquartet ρ).eval (star ρ) = 0 := by simp [Rquartet]

lemma Rquartet_eval_oneMinus (ρ : ℂ) :
    (Rquartet ρ).eval (1 - ρ) = 0 := by simp [Rquartet]

lemma Rquartet_eval_oneMinus_star (ρ : ℂ) :
    (Rquartet ρ).eval (1 - star ρ) = 0 := by simp [Rquartet]

end XiPacket
end Targets
end Hyperlocal
