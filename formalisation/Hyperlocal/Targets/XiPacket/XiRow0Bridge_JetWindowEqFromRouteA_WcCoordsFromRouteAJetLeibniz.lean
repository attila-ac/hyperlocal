/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcCoordsFromRouteAJetLeibniz.lean
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]

namespace JetQuotOp

private lemma isJet3At_wc_routeA (s : OffSeed Xi) :
    IsJet3At (routeA_G s) (1 - s.ρ) (wc s) := by
  classical
  have H := JetQuotOpTheorem.xiRouteA_jetPkg_jet3 (s := s) (z := (1 - s.ρ))
  have hjet :
      IsJet3At (routeA_G s) (1 - s.ρ) (jet3 (routeA_G s) (1 - s.ρ)) :=
    H.2.1
  simpa [wc_eq_jet3_routeA (s := s)] using hjet

lemma wc_0_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨0, by decide⟩ = (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.1

lemma wc_1_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨1, by decide⟩ = deriv (routeA_G s) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.1

lemma wc_2_from_routeAJetPkg (s : OffSeed Xi) :
    wc s ⟨2, by decide⟩ = deriv (deriv (routeA_G s)) (1 - s.ρ) := by
  have hIsJet := isJet3At_wc_routeA (s := s)
  simpa using hIsJet.2.2

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
