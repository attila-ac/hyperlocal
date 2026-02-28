/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTrueAnalytic.lean

  "Sigma provider" for AtOrder windows:
  build Row0ConvolutionAtRev for each canonical AtOrder window
  and discharge to row0Sigma = 0 via the pure-algebra lemma
  row0Sigma_eq_zero_from_Row0ConvolutionAtRev.

  NOTE:
  This depends on whatever is used to build Row0ConvolutionAtRev for AtOrder windows.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-!
## Sigma lemmas for the three canonical AtOrder windows

We use:
  * row0ConvolutionAtRev_w0At/wp2At/wp3At
  * row0Sigma_eq_zero_from_Row0ConvolutionAtRev
-/

theorem sigma_w0At
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (w0At m s) = 0 := by
  have H0 : Row0ConvolutionAtRev s (s.ρ) (w0At m s) :=
    row0ConvolutionAtRev_w0At (m := m) (s := s)
  simpa using
    (row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) H0)

theorem sigma_wp2At
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp2At m s) = 0 := by
  have H0 : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
    row0ConvolutionAtRev_wp2At (m := m) (s := s)
  simpa using
    (row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H0)

theorem sigma_wp3At
    (m : ℕ) (s : OffSeed Xi) : row0Sigma s (wp3At m s) = 0 := by
  have H0 : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
    row0ConvolutionAtRev_wp3At (m := m) (s := s)
  simpa using
    (row0Sigma_eq_zero_from_Row0ConvolutionAtRev
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) H0)

/-- Provider instance. -/
instance : XiAtOrderSigmaProvider where
  sigma m s :=
    { hw0AtSigma  := sigma_w0At  (m := m) (s := s)
      hwp2AtSigma := sigma_wp2At (m := m) (s := s)
      hwp3AtSigma := sigma_wp3At (m := m) (s := s) }

end XiPacket
end Targets
end Hyperlocal
