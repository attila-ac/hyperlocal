import Hyperlocal.Targets.XiRow0SigmaWcZeroOnResonantBranchClosed
import Hyperlocal.Targets.XiSin2ProviderFromEquivalentResonantBranchSeams
import Hyperlocal.Targets.XiNoOffSeedDirectFromOnePrimeSineOnResonantBranch
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
The sharp resonant jet-packet equality theorem already forces the prime-2
resonant sine theorem.

So `hpack_res` is strictly stronger than the one-prime endgame criterion.
-/
theorem sin2_zero_on_resonant_branch_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  letI : XiRow0SigmaWcZeroOnResonantBranchProvider :=
    instXiRow0SigmaWcZeroOnResonantBranchProviderInstalled
      (hsigma_res :=
        row0Sigma_wc_zero_on_resonant_branch_closed
          (hpack_res := hpack_res))
  exact sin2_zero_on_resonant_branch_of_row0Sigma_wc_provider

/--
Xi-side final export from the sharp resonant jet-packet equality theorem,
now routed through the strictly smaller one-prime sine criterion.
-/
theorem noOffSeed_Xi_final_of_resonant_jetPacketEq_via_sin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin2_zero_on_resonant_branch_of_resonant_jetPacketEq
        (hpack_res := hpack_res))

/--
ζ-side final export from the sharp resonant jet-packet equality theorem,
via the strictly smaller one-prime sine criterion.
-/
theorem noOffSeed_Zeta_final_of_resonant_jetPacketEq_via_sin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin2_zero_on_resonant_branch_of_resonant_jetPacketEq
        (hpack_res := hpack_res))

/--
RH-facing final export from the sharp resonant jet-packet equality theorem,
via the strictly smaller one-prime sine criterion.
-/
theorem criticalzero_zeta_final_of_resonant_jetPacketEq_via_sin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sin2_zero_on_resonant_branch
    (h2_res :=
      sin2_zero_on_resonant_branch_of_resonant_jetPacketEq
        (hpack_res := hpack_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
