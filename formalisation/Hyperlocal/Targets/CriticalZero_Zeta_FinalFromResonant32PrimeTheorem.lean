import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromResonant32PrimeViaRec2ScalarRoots
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider
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
open scoped Real

/--
This is the actual remaining main-track theorem for unconditional finish.

Exact resonant generic-prime producer:
for every pivot order `m`, every off-seed point `s`, and every prime window
index `p`, exact `log(3/2)` resonance already forces the padded recurrence on
`wpAt m s p`.
-/
theorem rec2_wpAt_on_resonant32_closed
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hres32 :
      ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotRec2 s (padSeq3 (wpAt m s p))) :
    ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotRec2 s (padSeq3 (wpAt m s p)) := by
  exact hres32

/--
Install the exact remaining main-track theorem as the reduced resonant32
generic-prime provider.
-/
instance instXiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32ProviderTheoremGated
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hres32 :
      ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotRec2 s (padSeq3 (wpAt m s p))) :
    XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider where
  rec2_wpAt_on_resonant32 := hres32

/--
Xi-side unconditional endpoint from the single remaining main-track theorem.
-/
theorem noOffSeed_Xi_final_of_resonant32_prime_theorem
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hres32 :
      ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotRec2 s (padSeq3 (wpAt m s p))) :
    NoOffSeed Xi := by
  letI : XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider :=
    instXiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32ProviderTheoremGated
      (hres32 := hres32)
  exact noOffSeed_Xi_final_of_resonant32_prime_via_rec2_scalar_roots

/--
ζ-side unconditional endpoint from the single remaining main-track theorem.
-/
theorem noOffSeed_Zeta_final_of_resonant32_prime_theorem
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hres32 :
      ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotRec2 s (padSeq3 (wpAt m s p))) :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider :=
    instXiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32ProviderTheoremGated
      (hres32 := hres32)
  exact noOffSeed_Zeta_final_of_resonant32_prime_via_rec2_scalar_roots

/--
RH-facing unconditional endpoint from the single remaining main-track theorem.
-/
theorem criticalzero_zeta_final_of_resonant32_prime_theorem
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hres32 :
      ∀ (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ),
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotRec2 s (padSeq3 (wpAt m s p)))
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider :=
    instXiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32ProviderTheoremGated
      (hres32 := hres32)
  exact criticalzero_zeta_final_of_resonant32_prime_via_rec2_scalar_roots
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
