/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetPkgFromAnalyticInputs.lean

  Theorem-level (extractor-free) Route-A jet *package* derived from `XiAnalyticInputs`.

  IMPORTANT:
  This module deliberately targets the *canonical* raw-derivative jet window `jet3 G z`.
  It does not (yet) identify the definitional ξ-windows `w0/wc/wp2/wp3` or the
  jet-pivot windows `w0At/wp2At/wp3At` as jets of the quotient `G`.

  Once window=jet lemmas are available, the Route–A window=jet bridge axioms in XiRow0Bridge_JetWindowEqFromRouteA.lean can be replaced by theorems, fully eliminating the remaining Route–A axiomatic boundary.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAt_Discharge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace JetQuotOp

/--
Theorem-level Route-A jet package at the *canonical* jet window.

This is the clean analytic content you can obtain today:
* existence of the quartet quotient `G` (from `XiAnalyticInputs`),
* global differentiability (from entireness / analyticity),
* a jet witness for the *canonical* jet window `jet3 G z`.
-/
theorem xiRouteA_jetPkg_jet3 (s : OffSeed Xi) (z : ℂ) :
    ∃ G : ℂ → ℂ,
      Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
      IsJet3At G z (jet3 G z) ∧
      Differentiable ℂ (Rfun s) ∧
      Differentiable ℂ G ∧
      Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
      Differentiable ℂ (fun t => deriv G t) := by
  classical
  rcases G_Xi_entire s with ⟨G, hfac, hG_entire⟩
  refine ⟨G, hfac, ?_, ?_, ?_, ?_, ?_⟩
  · exact isJet3At_jet3 G z
  · exact Rfun_differentiable s
  · exact G_differentiable_of_entire hG_entire
  · exact Rfun_deriv_differentiable s
  · exact G_deriv_differentiable_of_entire hG_entire

end JetQuotOp

end XiPacket
end Targets
end Hyperlocal
