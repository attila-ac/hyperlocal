/-
  Hyperlocal/Targets/XiPacket/XiAnalyticInputs_Factorization.lean

  Route-A factorisation handoff layer.

  This file:
  * builds the patched quotient `G`
  * proves `FactorisedByQuartet xi ρ 1 G`
  * proves `EntireFun G` via `entire_G_of_factorisation`

  All orbit-geometry is in `XiOrbitGeometry.lean`.
  The local factor lemma is isolated in `XiLocalFactor.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiOrbitGeometry
import Hyperlocal.Targets.XiPacket.XiLocalFactor

import Hyperlocal.FactorizationGofSEntire
import Hyperlocal.Factorization
import Hyperlocal.Removable  -- still useful elsewhere, but we don't depend on its lemma name

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Topology
open Hyperlocal.Factorization
open Hyperlocal.GrowthOrder
open Hyperlocal.FactorizationGofSEntire
open Hyperlocal.FactorizationAnalytic

/-- Patched quotient: equals `xi z / R.eval z` off the quartet, and uses 4 chosen values on orbit points. -/
private def Gpatched (ρ : ℂ) (gρ gρc g1m g1mc : ℂ) : ℂ → ℂ :=
  fun z =>
    if z = ρ then gρ
    else if z = (starRingEnd ℂ) ρ then gρc
    else if z = oneMinus ρ then g1m
    else if z = oneMinus ((starRingEnd ℂ) ρ) then g1mc
    else xi z / (Factorization.Rρk ρ 1).eval z

private lemma Gpatched_eq_div_off
    {ρ gρ gρc g1m g1mc z : ℂ}
    (h1 : z ≠ ρ)
    (h2 : z ≠ (starRingEnd ℂ) ρ)
    (h3 : z ≠ oneMinus ρ)
    (h4 : z ≠ oneMinus ((starRingEnd ℂ) ρ)) :
    Gpatched ρ gρ gρc g1m g1mc z =
      xi z / (Factorization.Rρk ρ 1).eval z := by
  simp [Gpatched, h1, h2, h3, h4]

theorem Xi_exists_factorisedByQuartet_entire (s : OffSeed xi) :
    ∃ G : ℂ → ℂ, FactorisedByQuartet xi s.ρ 1 G ∧ GrowthOrder.EntireFun G := by
  classical
  set ρ : ℂ := s.ρ

  have hquart :
      xi ρ = 0 ∧
      xi ((starRingEnd ℂ) ρ) = 0 ∧
      xi (oneMinus ρ) = 0 ∧
      xi (oneMinus ((starRingEnd ℂ) ρ)) = 0 := by
    simpa [ρ] using seed_gives_quartet xi Xi_FE Xi_RC s

  rcases xi_localFactor (a := ρ) hquart.1 with ⟨Jρ, Jρ_an, Jρ_eq⟩
  rcases xi_localFactor (a := (starRingEnd ℂ) ρ) hquart.2.1 with ⟨Jρc, Jρc_an, Jρc_eq⟩
  rcases xi_localFactor (a := oneMinus ρ) hquart.2.2.1 with ⟨J1m, J1m_an, J1m_eq⟩
  rcases xi_localFactor (a := oneMinus ((starRingEnd ℂ) ρ)) hquart.2.2.2 with ⟨J1mc, J1mc_an, J1mc_eq⟩

  let gρ : ℂ := Jρ ρ / W_at_rho ρ 1 ρ
  let gρc : ℂ :=
    Jρc ((starRingEnd ℂ) ρ) / W_at_rho ((starRingEnd ℂ) ρ) 1 ((starRingEnd ℂ) ρ)
  let g1m : ℂ := J1m (oneMinus ρ) / W_at_rho (oneMinus ρ) 1 (oneMinus ρ)
  let g1mc : ℂ :=
    J1mc (oneMinus ((starRingEnd ℂ) ρ)) /
      W_at_rho (oneMinus ((starRingEnd ℂ) ρ)) 1 (oneMinus ((starRingEnd ℂ) ρ))

  let G : ℂ → ℂ := Gpatched ρ gρ gρc g1m g1mc

  have hfac : FactorisedByQuartet xi ρ 1 G := by
    intro z
    by_cases hzρ : z = ρ
    · subst hzρ
      have hR : (Factorization.Rρk ρ 1).eval ρ = 0 := by
        simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
          Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin]
      simp [G, Gpatched, hR, hquart.1]
    · by_cases hzρc : z = (starRingEnd ℂ) ρ
      · subst hzρc
        have hR : (Factorization.Rρk ρ 1).eval ((starRingEnd ℂ) ρ) = 0 := by
          simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
            Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin]
        simp [G, Gpatched, hR, hquart.2.1, hzρ]
      · by_cases hz1m : z = oneMinus ρ
        · subst hz1m
          have hR : (Factorization.Rρk ρ 1).eval (oneMinus ρ) = 0 := by
            simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
              Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin]
          simp [G, Gpatched, hR, hquart.2.2.1, hzρ, hzρc]
        · by_cases hz1mc : z = oneMinus ((starRingEnd ℂ) ρ)
          · subst hz1mc
            have hR : (Factorization.Rρk ρ 1).eval (oneMinus ((starRingEnd ℂ) ρ)) = 0 := by
              simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
                Hyperlocal.MinimalModel.linPow, Hyperlocal.MinimalModel.lin]
            simp [G, Gpatched, hR, hquart.2.2.2, hzρ, hzρc, hz1m]
          ·
            have hzR :
                (Factorization.Rρk ρ 1).eval z ≠ 0 :=
              eval_Rρk_ne_zero_off ρ z 1 hzρ hzρc hz1m hz1mc
            have hG :
                G z = xi z / (Factorization.Rρk ρ 1).eval z :=
              Gpatched_eq_div_off
                (ρ := ρ) (gρ := gρ) (gρc := gρc) (g1m := g1m) (g1mc := g1mc)
                hzρ hzρc hz1m hz1mc
            simp [hG]
            field_simp [hzR]

  have hEntire : GrowthOrder.EntireFun G := by
    have H_an : ∀ z : ℂ, AnalyticAt ℂ xi z := by
      intro z
      exact Xi_entire (z := z)

    have hfac_conj : FactorisedByQuartet xi ((starRingEnd ℂ) ρ) 1 G := by
      intro z
      simpa [Rρk_conj_eq (ρ := ρ) (k := 1)] using (hfac z)

    have hfac_1m : FactorisedByQuartet xi (oneMinus ρ) 1 G := by
      intro z
      simpa [Rρk_oneMinus_eq (ρ := ρ) (k := 1)] using (hfac z)

    have hfac_1mc : FactorisedByQuartet xi (oneMinus ((starRingEnd ℂ) ρ)) 1 G := by
      intro z
      simpa [Rρk_oneMinus_conj_eq (ρ := ρ) (k := 1)] using (hfac z)

    -- local packages (exactly the shapes `entire_G_of_factorisation` wants)
    have locρ :
        ∃ J, AnalyticAt ℂ J ρ ∧ (∀ z, xi z = (z - ρ)^1 * J z) ∧
          ρ ≠ (starRingEnd ℂ) ρ ∧ ρ ≠ oneMinus ρ ∧ ρ ≠ oneMinus ((starRingEnd ℂ) ρ) ∧
          G ρ = J ρ / W_at_rho ρ 1 ρ := by
      refine ⟨Jρ, Jρ_an, ?_, ?_, ?_, ?_, ?_⟩
      · intro z; simpa [pow_one, mul_assoc] using (Jρ_eq z)
      · simpa [ρ] using offSeed_ne_conj s
      · simpa [ρ] using offSeed_ne_oneMinus s
      · simpa [ρ] using offSeed_ne_oneMinus_conj s
      · simp [G, Gpatched, gρ]

    have locρc :
        ∃ J, AnalyticAt ℂ J ((starRingEnd ℂ) ρ) ∧
          (∀ z, xi z = (z - (starRingEnd ℂ) ρ)^1 * J z) ∧
          (starRingEnd ℂ) ρ ≠ ρ ∧
          (starRingEnd ℂ) ρ ≠ oneMinus ρ ∧
          (starRingEnd ℂ) ρ ≠ oneMinus ((starRingEnd ℂ) ρ) ∧
          G ((starRingEnd ℂ) ρ) =
            J ((starRingEnd ℂ) ρ) / W_at_rho ((starRingEnd ℂ) ρ) 1 ((starRingEnd ℂ) ρ) := by
      refine ⟨Jρc, Jρc_an, ?_, ?_, ?_, ?_, ?_⟩
      · intro z; simpa [pow_one, mul_assoc] using (Jρc_eq z)
      · simpa [ρ] using offSeed_conj_ne s
      · -- conj ρ ≠ oneMinus ρ (critical line contradiction; keep it local)
        intro h
        have hRe : ((starRingEnd ℂ) ρ).re = (oneMinus ρ).re := congrArg Complex.re h
        have : ρ.re = 1 - ρ.re := by simpa [Hyperlocal.oneMinus] using hRe
        have hre : ρ.re = (1 / 2 : ℝ) := by linarith
        exact s.hσ (by simpa [ρ] using hre)
      · -- conj ρ ≠ oneMinus (conj ρ)
        have : (starRingEnd ℂ) ρ ≠ oneMinus ((starRingEnd ℂ) ρ) := by
          simpa [eq_comm, ρ] using offSeed_oneMinus_conj_ne_conj s
        exact this
      ·
        have hne : (starRingEnd ℂ) ρ ≠ ρ := by simpa [ρ] using offSeed_conj_ne s
        simp [G, Gpatched, gρc, hne]

    have loc1m :
        ∃ J, AnalyticAt ℂ J (oneMinus ρ) ∧
          (∀ z, xi z = (z - oneMinus ρ)^1 * J z) ∧
          oneMinus ρ ≠ ρ ∧ oneMinus ρ ≠ (starRingEnd ℂ) ρ ∧
          oneMinus ρ ≠ oneMinus ((starRingEnd ℂ) ρ) ∧
          G (oneMinus ρ) =
            J (oneMinus ρ) / W_at_rho (oneMinus ρ) 1 (oneMinus ρ) := by
      refine ⟨J1m, J1m_an, ?_, ?_, ?_, ?_, ?_⟩
      · intro z; simpa [pow_one, mul_assoc] using (J1m_eq z)
      · simpa [ρ] using offSeed_oneMinus_ne s
      · -- oneMinus ρ ≠ conj ρ
        intro h
        have hRe : (oneMinus ρ).re = ((starRingEnd ℂ) ρ).re := congrArg Complex.re h
        have : 1 - ρ.re = ρ.re := by simpa [Hyperlocal.oneMinus] using hRe
        have hre : ρ.re = (1 / 2 : ℝ) := by linarith
        exact s.hσ (by simpa [ρ] using hre)
      · -- oneMinus ρ ≠ oneMinus (conj ρ)  (FIX: orientation)
        simpa [eq_comm, ρ] using offSeed_oneMinus_conj_ne_oneMinus s
      ·
        have hne1 : oneMinus ρ ≠ ρ := by simpa [ρ] using offSeed_oneMinus_ne s
        have hne2 : oneMinus ρ ≠ (starRingEnd ℂ) ρ := by
          intro h
          have hRe : (oneMinus ρ).re = ((starRingEnd ℂ) ρ).re := congrArg Complex.re h
          have : 1 - ρ.re = ρ.re := by simpa [Hyperlocal.oneMinus] using hRe
          have hre : ρ.re = (1 / 2 : ℝ) := by linarith
          exact s.hσ (by simpa [ρ] using hre)
        simp [G, Gpatched, g1m, hne1, hne2]

    have loc1mc :
        ∃ J, AnalyticAt ℂ J (oneMinus ((starRingEnd ℂ) ρ)) ∧
          (∀ z, xi z = (z - oneMinus ((starRingEnd ℂ) ρ))^1 * J z) ∧
          oneMinus ((starRingEnd ℂ) ρ) ≠ ρ ∧
          oneMinus ((starRingEnd ℂ) ρ) ≠ (starRingEnd ℂ) ρ ∧
          oneMinus ((starRingEnd ℂ) ρ) ≠ oneMinus ρ ∧
          G (oneMinus ((starRingEnd ℂ) ρ)) =
            J (oneMinus ((starRingEnd ℂ) ρ)) /
              W_at_rho (oneMinus ((starRingEnd ℂ) ρ)) 1 (oneMinus ((starRingEnd ℂ) ρ)) := by
      refine ⟨J1mc, J1mc_an, ?_, ?_, ?_, ?_, ?_⟩
      · intro z; simpa [pow_one, mul_assoc] using (J1mc_eq z)
      · simpa [ρ] using offSeed_oneMinus_conj_ne s
      · simpa [ρ] using offSeed_oneMinus_conj_ne_conj s
      · simpa [ρ] using offSeed_oneMinus_conj_ne_oneMinus s
      ·
        have hne1 : oneMinus ((starRingEnd ℂ) ρ) ≠ ρ := by
          simpa [ρ] using offSeed_oneMinus_conj_ne s
        have hne2 : oneMinus ((starRingEnd ℂ) ρ) ≠ (starRingEnd ℂ) ρ := by
          simpa [ρ] using offSeed_oneMinus_conj_ne_conj s
        have hne3 : oneMinus ((starRingEnd ℂ) ρ) ≠ oneMinus ρ := by
          simpa [ρ] using offSeed_oneMinus_conj_ne_oneMinus s
        simp [G, Gpatched, g1mc, hne1, hne2, hne3]

    exact entire_G_of_factorisation
      (H := xi) (G := G) (rho := ρ) (k := 1)
      hfac hfac_conj hfac_1m hfac_1mc
      H_an locρ locρc loc1m loc1mc

  exact ⟨G, hfac, hEntire⟩

theorem G_Xi_entire (s : OffSeed xi) :
    ∃ G : ℂ → ℂ, FactorisedByQuartet xi s.ρ 1 G ∧ GrowthOrder.EntireFun G := by
  exact Xi_exists_factorisedByQuartet_entire s

end XiPacket
end Targets
end Hyperlocal
