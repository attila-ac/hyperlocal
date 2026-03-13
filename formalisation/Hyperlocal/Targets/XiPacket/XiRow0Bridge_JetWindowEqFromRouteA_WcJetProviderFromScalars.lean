import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_WcNormalization
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

namespace JetQuotOp

private theorem xiRouteA_jetPkg_jet3_local
    (s : OffSeed Xi) (z : ℂ) :
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 (routeA_G s) ∧
    IsJet3At (routeA_G s) z (jet3 (routeA_G s) z) ∧
    Differentiable ℂ (Rfun s) ∧
    Differentiable ℂ (routeA_G s) ∧
    Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
    Differentiable ℂ (fun t => deriv (routeA_G s) t) := by
  classical
  refine ⟨routeA_G_factorised s, ?_, ?_, ?_, ?_, ?_⟩
  · exact isJet3At_jet3 (routeA_G s) z
  · exact Rfun_differentiable s
  · exact G_differentiable_of_entire (routeA_G_entire s)
  · exact Rfun_deriv_differentiable s
  · exact G_deriv_differentiable_of_entire (routeA_G_entire s)

theorem routeA_G_wc_coord0
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (routeA_G s) (1 - s.ρ) = wc s (0 : Fin 3) := by
  calc
    (routeA_G s) (1 - s.ρ) = 0 := routeA_G_at_one_sub_rho (s := s)
    _ = wc s (0 : Fin 3) := by
      symm
      simpa using (ToeplitzGuardrails.wc_apply_fin0 (s := s))

theorem routeA_G_wc_coord1
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    deriv (routeA_G s) (1 - s.ρ) = wc s (1 : Fin 3) := by
  calc
    deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) := routeA_G_deriv_at_one_sub_rho (s := s)
    _ = wc s (1 : Fin 3) := by
      symm
      simpa using (ToeplitzGuardrails.wc_apply_fin1 (s := s))

theorem routeA_G_wc_coord2
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    deriv (deriv (routeA_G s)) (1 - s.ρ) = wc s (2 : Fin 3) := by
  calc
    deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ) :=
      routeA_G_deriv2_at_one_sub_rho (s := s)
    _ = wc s (2 : Fin 3) := by
      symm
      simpa using (ToeplitzGuardrails.wc_apply_fin2 (s := s))

theorem wc_isJet3At_routeA
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  constructor
  · symm
    exact routeA_G_wc_coord0 (s := s)
  constructor
  · symm
    exact routeA_G_wc_coord1 (s := s)
  · symm
    exact routeA_G_wc_coord2 (s := s)

instance (priority := 1000)
    [TAC.XiJetWindowEqAtOrderQuotProvider] : RouteAWcJetProvider where
  jet_wc := by
    intro s
    exact wc_isJet3At_routeA (s := s)

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
