/-
  Hyperlocal/Targets/XiNoOffSeedDirectFromOnePrimeSineOnResonantBranch.lean

  Sharpest current last-mile contraction inside the two-prime mechanism:

  because the previous file reduced the endgame to proving just ONE prime
  coefficient vanishing on the exact resonance branch, and because

      bCoeff σ t p = pSigma σ p * sin(t log p),

  it is actually enough to prove just ONE prime sine vanishing on the exact
  resonance branch:

      ∀ s, sin(t log(3/2)) = 0 -> sin(t log 2) = 0
  or
      ∀ s, sin(t log(3/2)) = 0 -> sin(t log 3) = 0.

  Once either one is known, the previous resonant-branch file closes the
  Xi-side contradiction and hence the RH-facing zeta endpoint.
-/

import Hyperlocal.Targets.XiNoOffSeedDirectFromOnePrimeOnResonantBranch
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion
open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Resonant-branch prime-2 sine vanishing already suffices for `NoOffSeed Xi`.
-/
theorem noOffSeed_Xi_of_sin2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_bCoeff2_zero_on_resonant_branch
    (hb2_res := by
      intro s hres
      have h2 : Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := h2_res s hres
      simp [bCoeff, h2])

/--
Resonant-branch prime-3 sine vanishing already suffices for `NoOffSeed Xi`.
-/
theorem noOffSeed_Xi_of_sin3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_bCoeff3_zero_on_resonant_branch
    (hb3_res := by
      intro s hres
      have h3 : Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := h3_res s hres
      simp [bCoeff, h3])

/--
ζ-side transfer from the resonant-branch prime-2 sine criterion.
-/
theorem noOffSeed_Zeta_of_sin2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_sin2_zero_on_resonant_branch (h2_res := h2_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
RH-facing export from the resonant-branch prime-2 sine criterion.
-/
theorem criticalzero_zeta_of_sin2_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_sin2_zero_on_resonant_branch (h2_res := h2_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
ζ-side transfer from the resonant-branch prime-3 sine criterion.
-/
theorem noOffSeed_Zeta_of_sin3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_sin3_zero_on_resonant_branch (h3_res := h3_res)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
RH-facing export from the resonant-branch prime-3 sine criterion.
-/
theorem criticalzero_zeta_of_sin3_zero_on_resonant_branch
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_sin3_zero_on_resonant_branch (h3_res := h3_res)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
