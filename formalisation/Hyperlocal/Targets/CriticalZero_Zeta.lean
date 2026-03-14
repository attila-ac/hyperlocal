/-
  Hyperlocal/Targets/CriticalZero_Zeta.lean

  Final ζ-facing exports.

  This file packages:
    * `noOffSeed_Zeta`
    * `criticalzero_zeta`

  from the existing staged Xi-side chain

      offSeedPhaseLock_Xi -> noOffSeed_xi_of_phaseLock

  together with `Targets.ZetaTransfer`.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.Stage3SystemXiProof
import Hyperlocal.Targets.ZetaTransfer
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Conclusion.OffSeedToTAC
open Complex

/-- Final ζ-facing export. -/
theorem noOffSeed_Zeta
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [_root_.Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
        (-2 : ℂ) * deriv (deriv (Hyperlocal.Targets.XiPacket.routeA_G s)) (1 - s.ρ)
          + (Hyperlocal.Targets.XiPacket.JetQuotOp.σ2 s) *
              deriv (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ)
          - (Hyperlocal.Targets.XiPacket.JetQuotOp.σ3 s) *
              (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hlock : Hyperlocal.Transport.OffSeedPhaseLock (H := Hyperlocal.Targets.Xi) := by
    simpa [Hyperlocal.Targets.Xi, Hyperlocal.Targets.XiPacket.Xi] using
      (Hyperlocal.Targets.offSeedPhaseLock_Xi (hroute := hroute))

  have hxi : NoOffSeed Hyperlocal.Targets.Xi := by
    exact Hyperlocal.Targets.noOffSeed_xi_of_phaseLock (hlock := hlock)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/-- Final RH-facing pointwise export for ζ. -/
theorem criticalzero_zeta
    [Hyperlocal.Targets.XiPacket.XiJetQuotRec2AtOrderTrueAnalytic]
    [_root_.Hyperlocal.Targets.XiPacket.TAC.XiJetWindowEqAtOrderQuotProvider]
    [_root_.Hyperlocal.Targets.XiPacket.RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Hyperlocal.Targets.XiPacket.Xi,
        (-2 : ℂ) * deriv (deriv (Hyperlocal.Targets.XiPacket.routeA_G s)) (1 - s.ρ)
          + (Hyperlocal.Targets.XiPacket.JetQuotOp.σ2 s) *
              deriv (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ)
          - (Hyperlocal.Targets.XiPacket.JetQuotOp.σ3 s) *
              (Hyperlocal.Targets.XiPacket.routeA_G s) (1 - s.ρ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  by_contra hcrit
  have hz_off : Hyperlocal.OffSeed Hyperlocal.zeta :=
    { ρ := ρ
      hρ := hζ
      hσ := hcrit
      ht := hIm }
  exact (noOffSeed_Zeta (hroute := hroute)) ⟨hz_off⟩

end Targets
end Hyperlocal
