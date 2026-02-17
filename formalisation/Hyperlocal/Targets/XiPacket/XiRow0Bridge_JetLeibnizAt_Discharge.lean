/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizAt_Discharge.lean

  Discharge (Route-L / Leibniz) at the *canonical raw jet* constructed from the
  Route-A factor `G` supplied by `G_Xi_entire`.

  This file does NOT yet identify the canonical ξ-windows `w0/wc/wp2/wp3` as
  jets of that `G`; it only proves that for the jet window `jet3 G z` built
  from raw derivatives, the Leibniz semantic predicate holds.

  Once you add “window = jet” lemmas for `w0/wc/wp2/wp3`, you can transport this
  discharge to the canonical windows and remove the temporary axioms in
  `XiRow0Bridge_JetLeibnizAtFromRouteA.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.FactorizationGofSAnalytic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators

/-- Canonical raw-derivative jet window of length 3 for `G` at `z`. -/
def jet3 (G : ℂ → ℂ) (z : ℂ) : Transport.Window 3 :=
  fun i =>
    match i.1 with
    | 0 => G z
    | 1 => deriv G z
    | _ => deriv (deriv G) z

lemma isJet3At_jet3 (G : ℂ → ℂ) (z : ℂ) :
    IsJet3At G z (jet3 G z) := by
  constructor
  · rfl
  constructor
  · -- index 1
    change (jet3 G z ⟨1, by decide⟩) = deriv G z
    simp [jet3]
  · -- index 2
    change (jet3 G z ⟨2, by decide⟩) = deriv (deriv G) z
    simp [jet3]

/-- `Rfun s` is analytic everywhere, hence differentiable everywhere. -/
lemma Rfun_differentiable (s : OffSeed Xi) : Differentiable ℂ (Rfun s) := by
  intro z
  have hA :
      AnalyticAt ℂ (fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t) z :=
    Hyperlocal.FactorizationAnalytic.analyticAt_eval_Rρk_as_product
      (ρ := s.ρ) (k := 1) (z := z)
  simpa [Rfun] using hA.differentiableAt

/-- `t ↦ deriv (Rfun s) t` is differentiable everywhere. -/
lemma Rfun_deriv_differentiable (s : OffSeed Xi) :
    Differentiable ℂ (fun t => deriv (Rfun s) t) := by
  intro z
  have hR : AnalyticAt ℂ (Rfun s) z := by
    have hA :
        AnalyticAt ℂ (fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t) z :=
      Hyperlocal.FactorizationAnalytic.analyticAt_eval_Rρk_as_product
        (ρ := s.ρ) (k := 1) (z := z)
    simpa [Rfun] using hA
  exact (hR.deriv).differentiableAt

/-- If `G` is entire, then `G` is differentiable everywhere. -/
lemma G_differentiable_of_entire {G : ℂ → ℂ} (hG : Hyperlocal.GrowthOrder.EntireFun G) :
    Differentiable ℂ G := by
  intro z
  exact (hG z).differentiableAt

/-- If `G` is entire, then `t ↦ deriv G t` is differentiable everywhere. -/
lemma G_deriv_differentiable_of_entire {G : ℂ → ℂ} (hG : Hyperlocal.GrowthOrder.EntireFun G) :
    Differentiable ℂ (fun t => deriv G t) := by
  intro z
  exact ((hG z).deriv).differentiableAt

/--
Discharge lemma (canonical jet):

Route-A supplies an entire factor `G` with `Xi = Rfun s * G`,
so the canonical raw jet `jet3 G z` satisfies `JetLeibnizAt s z`.
-/
theorem jetLeibnizAt_discharge_at
    (s : OffSeed Xi) (z : ℂ) :
    ∃ G : ℂ → ℂ, JetLeibnizAt s z (jet3 G z) := by
  classical
  rcases G_Xi_entire s with ⟨G, hfac, hG_entire⟩
  have hjet : IsJet3At G z (jet3 G z) := isJet3At_jet3 G z
  have hR  : Differentiable ℂ (Rfun s) := Rfun_differentiable s
  have hG  : Differentiable ℂ G := G_differentiable_of_entire hG_entire
  have hR' : Differentiable ℂ (fun t => deriv (Rfun s) t) := Rfun_deriv_differentiable s
  have hG' : Differentiable ℂ (fun t => deriv G t) := G_deriv_differentiable_of_entire hG_entire
  refine ⟨G, ?_⟩
  refine ⟨G, hfac, hjet, ?_, ?_, ?_⟩
  · exact (jetLeibnizAt_of_factorised s z (jet3 G z) G hfac hjet hR hG hR' hG').1
  · exact (jetLeibnizAt_of_factorised s z (jet3 G z) G hfac hjet hR hG hR' hG').2.1
  · exact (jetLeibnizAt_of_factorised s z (jet3 G z) G hfac hjet hR hG hR' hG').2.2

end XiPacket
end Targets
end Hyperlocal
