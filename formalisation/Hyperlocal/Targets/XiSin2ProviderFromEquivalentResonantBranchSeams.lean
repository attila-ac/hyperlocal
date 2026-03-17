import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderBridges
import Hyperlocal.Targets.XiNoOffSeedDirectFromResonantBranchSeams
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Provider surface for the resonant-branch equivalent local form (A):
`row0Sigma s (wc s) = 0`.
-/
class XiRow0SigmaWcZeroOnResonantBranchProvider : Prop where
  row0Sigma_wc_zero_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0

/--
Installer from an explicit theorem input for resonant-branch form (A).
-/
instance instXiRow0SigmaWcZeroOnResonantBranchProviderInstalled
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    XiRow0SigmaWcZeroOnResonantBranchProvider where
  row0Sigma_wc_zero_on_resonant_branch := hsigma_res

/-- Consumer wrapper for resonant-branch form (A). -/
theorem row0Sigma_wc_zero_on_resonant_branch_provided
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 :=
  XiRow0SigmaWcZeroOnResonantBranchProvider.row0Sigma_wc_zero_on_resonant_branch

/--
Equivalent local form (A) already forces the prime-2 resonant sine theorem.

This is the useful promotion:
(A) on the exact resonant branch -> `h2_res`.
After that, the existing bridge stack already gives
`XiWp5Row0ZeroOnResonantBranchProvider`.
-/
theorem sin2_zero_on_resonant_branch_of_row0Sigma_wc_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
      (hsigma_res := row0Sigma_wc_zero_on_resonant_branch_provided)
  exact False.elim (hno ⟨s⟩)

/--
Install the standard prime-2 resonant sine provider from resonant-branch form (A).

With this instance in scope, the already-existing instance bridge in
`XiWp5Row0ZeroOnResonantBranchProviderBridges.lean` closes the exact final
wp5 provider automatically.
-/
instance instXiSin2ZeroOnResonantBranchProviderOfRow0SigmaWc
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    XiSin2ZeroOnResonantBranchProvider where
  sin2_zero_on_resonant_branch :=
    sin2_zero_on_resonant_branch_of_row0Sigma_wc_provider

/--
Equivalent local form (C) already forces the prime-2 resonant sine theorem.

This is stronger than the old direct bridge
`(C) + bCoeff5 -> wp5`: once resonant-branch sigma2 is installed, the
contradiction argument itself supplies `h2_res`.
-/
theorem sin2_zero_on_resonant_branch_of_sigma2_eq_two_delta_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch
      (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_provided)
  exact False.elim (hno ⟨s⟩)

/--
Install the standard prime-2 resonant sine provider from resonant-branch form (C).

Again, once this instance is available, the existing sin2 -> wp5 bridge closes
the exact final provider surface automatically.
-/
instance instXiSin2ZeroOnResonantBranchProviderOfSigma2EqTwoDelta
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    XiSin2ZeroOnResonantBranchProvider where
  sin2_zero_on_resonant_branch :=
    sin2_zero_on_resonant_branch_of_sigma2_eq_two_delta_provider

end Targets
end Hyperlocal
