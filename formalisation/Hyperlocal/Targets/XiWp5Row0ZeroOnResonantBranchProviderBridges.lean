import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchAttempt
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Prime-2 last-mile provider on the exact `log(3/2)` resonant branch.
-/
class XiSin2ZeroOnResonantBranchProvider : Prop where
  sin2_zero_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0

/--
Prime-3 last-mile provider on the exact `log(3/2)` resonant branch.
-/
class XiSin3ZeroOnResonantBranchProvider : Prop where
  sin3_zero_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0

/--
Split pair-{2,5} scalar midpoint provider on the exact `log(3/2)` resonant branch.
-/
class XiSigma2EqTwoDeltaOnResonantBranchProvider : Prop where
  sigma2_eq_two_delta_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)

/--
Split pair-{2,5} prime-5 scalar provider on the exact `log(3/2)` resonant branch.
-/
class XiBCoeff5ZeroOnResonantBranchProvider : Prop where
  bCoeff5_zero_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0

/-- Consumer wrapper for the prime-2 resonant-branch provider. -/
theorem sin2_zero_on_resonant_branch_provided
    [XiSin2ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 :=
  XiSin2ZeroOnResonantBranchProvider.sin2_zero_on_resonant_branch

/-- Consumer wrapper for the prime-3 resonant-branch provider. -/
theorem sin3_zero_on_resonant_branch_provided
    [XiSin3ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 :=
  XiSin3ZeroOnResonantBranchProvider.sin3_zero_on_resonant_branch

/-- Consumer wrapper for the resonant-branch `σ2 = 2 * delta` provider. -/
theorem sigma2_eq_two_delta_on_resonant_branch_provided
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) :=
  XiSigma2EqTwoDeltaOnResonantBranchProvider.sigma2_eq_two_delta_on_resonant_branch

/-- Consumer wrapper for the resonant-branch `bCoeff(...,5)=0` provider. -/
theorem bCoeff5_zero_on_resonant_branch_provided
    [XiBCoeff5ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0 :=
  XiBCoeff5ZeroOnResonantBranchProvider.bCoeff5_zero_on_resonant_branch

/--
Bridge theorem:
a prime-2 resonant-branch sine provider already yields the exact final
`wpAt 0 s 5` row-0 resonant-branch theorem.
-/
theorem wp5_row0_zero_on_resonant_branch_of_sin2_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSin2ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  exact Hyperlocal.Targets.wp5_row0_zero_on_resonant_branch_all
    (h2_res := sin2_zero_on_resonant_branch_provided)

/--
Bridge theorem:
a prime-3 resonant-branch sine provider already yields the exact final
`wpAt 0 s 5` row-0 resonant-branch theorem.
-/
theorem wp5_row0_zero_on_resonant_branch_of_sin3_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSin3ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  exact Hyperlocal.Targets.wp5_row0_zero_on_resonant_branch_all_of_sin3
    (h3_res := sin3_zero_on_resonant_branch_provided)

/--
Bridge theorem:
the split pair-{2,5} scalar surface
  `σ2 = 2 * delta`
and
  `bCoeff(...,5) = 0`
already yields the exact final `wpAt 0 s 5` row-0 resonant-branch theorem.
-/
theorem wp5_row0_zero_on_resonant_branch_of_sigma2delta_bCoeff5_providers
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider]
    [XiBCoeff5ZeroOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  intro s hres
  exact Hyperlocal.Targets.XiPacket.W1.row0Sigma_wpAt5_eq_zero_of_sigma2_eq_two_delta_and_bCoeff5_zero
    (s := s)
    (hσ2δ := sigma2_eq_two_delta_on_resonant_branch_provided s hres)
    (hb5 := bCoeff5_zero_on_resonant_branch_provided s hres)

/--
Instance bridge:
prime-2 resonant-branch sine provider => exact final wp5-row0 provider.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderOfSin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSin2ZeroOnResonantBranchProvider] :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch :=
    wp5_row0_zero_on_resonant_branch_of_sin2_provider

/--
Instance bridge:
prime-3 resonant-branch sine provider => exact final wp5-row0 provider.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderOfSin3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSin3ZeroOnResonantBranchProvider] :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch :=
    wp5_row0_zero_on_resonant_branch_of_sin3_provider

/--
Instance bridge:
split pair-{2,5} scalar providers => exact final wp5-row0 provider.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderOfSigma2DeltaBCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider]
    [XiBCoeff5ZeroOnResonantBranchProvider] :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch :=
    wp5_row0_zero_on_resonant_branch_of_sigma2delta_bCoeff5_providers

end Targets
end Hyperlocal
