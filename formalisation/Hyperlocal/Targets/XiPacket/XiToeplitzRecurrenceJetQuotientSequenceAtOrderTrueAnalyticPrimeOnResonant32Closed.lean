import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider
import Hyperlocal.Targets.XiPacket.XiRouteA_WcScalarNormalizationProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport

/--
This is the actual last mathematical theorem on the unconditional main track.

Once this is proved, the existing instance in
`XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider`
upgrades it to the full generic-prime class, and the already-green final endpoint
files close the unconditional RH route.
-/
theorem rec2_wpAt_on_resonant32_closed
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    ∀ (m : ℕ) (s : OffSeed Xi) (p : ℕ),
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotRec2 s (padSeq3 (wpAt m s p)) := by
  intro m s p hres

  /-
  This is the true last-math insertion point.

  The intended attack should not go back upward into corridor wrappers.
  It should stay here, on the exact resonant branch, and prove the full
  generic-prime padded recurrence packet directly.

  Concrete mathematically honest subroutes that may close this proof:

  Route A (most direct to the stated theorem):
    prove toeplitz row-012 vanishing for `wpAt m s p`
    and then apply
      jetQuotRec2_padSeq3_of_toeplitzRow012Prop.

  Route B (via the local canonical packet seam):
    first show the resonant branch forces the canonical packet alignment
      wpAt m s p = w0At m s
    or an equivalent row012 consequence,
    then transport that to `JetQuotRec2`.

  Route C (via Route-A scalar normalization + local seam):
    use the current scalar-root / Route-A normalization infrastructure to
    prove the row012 Toeplitz frontier for arbitrary prime windows on the
    resonant branch, then convert by the row012->sequence bridge.

  Route D (via one-prime sine theorem as the actual local obstruction):
    prove the exact resonant one-prime sine theorem
      sin(t log (3/2)) = 0 -> sin(t log 2) = 0,
    then use the already-built local seam/provider chain to recover the
    generic-prime recurrence payload here.
  -/

  sorry

/--
Binder-free installation of the exact final resonant32 theorem.

After this instance is available, the file
`XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider.lean`
automatically upgrades it to the full class
`XiJetQuotRec2AtOrderTrueAnalyticPrime`.
-/
instance instXiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32ProviderClosed
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider where
  rec2_wpAt_on_resonant32 := rec2_wpAt_on_resonant32_closed

end XiPacket
end Targets
end Hyperlocal
