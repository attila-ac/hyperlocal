import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromResonantJetPacketEq
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
Xi-side final export from the single sharp resonant packet-equality theorem input.
-/
theorem noOffSeed_Xi_final_of_resonant_jetPacketEq_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Xi := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromResonantJetPacketEq
      (hpack_res := hpack_res)
  exact noOffSeed_Xi_final_of_corridor_provider

/--
ζ-side final export from the single sharp resonant packet-equality theorem input.
-/
theorem noOffSeed_Zeta_final_of_resonant_jetPacketEq_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromResonantJetPacketEq
      (hpack_res := hpack_res)
  exact noOffSeed_Zeta_final_of_corridor_provider

/--
RH-facing final export from the single sharp resonant packet-equality theorem input.
-/
theorem criticalzero_zeta_final_of_resonant_jetPacketEq_provider
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderInstalledFromResonantJetPacketEq
      (hpack_res := hpack_res)
  exact criticalzero_zeta_final_of_corridor_provider
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
