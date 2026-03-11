/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Discharge.lean

  Cycle-safe theorem-level discharge of the Row012 AtOrder reverse-stencil payload.

  DESIGN:
  * Use strengthened Route-B heart output for:
      - row0Sigma = 0  (gives convCoeff n=3)
  * Rebuild `Row012ExtraLin` theorem-level via `...FromHeart`.
  * Use Route-A jet package for witnesses (G, FactorisedByQuartet, IsJet3At).
  * Use algebraic closed forms from the pure-algebra Reduce file.

  CRITICAL (cycle safety):
  * MUST NOT import the RecurrenceA / analytic extractor stack.
  * MUST NOT import any sigma-provider *instance* modules here.
    (No `...SigmaProviderAnalytic`, no `...SigmaProviderFromRow0FrontierAtOrder`.)

  UPDATE (2026-03-11):
  We now expose explicit-coords theorems first, and keep the historical
  provider-based wrappers as compatibility shells. This localises the ambient
  `XiAtOrderCoords01Provider` dependency to a thin wrapper instead of the
  whole discharge corridor.

  2026-03-11:
  Retargeted from the legacy ambient Route-A Leibniz wrapper to the
  theorem-side wrapper with explicit gate
    [TAC.XiJetWindowEqAtOrderQuotProvider].
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromProvidedCoords
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Build Row012ConvolutionAtRev for `w0At m s` using heart constraints + Route-A witnesses. -/
theorem row012ConvolutionAtRev_w0At_fromHeart_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (HC : XiAtOrderCoords01Out m s) :
    Row012ConvolutionAtRev s s.ρ (w0At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromHeart_of_coords (m := m) (s := s) HC
  have HL : Row012ExtraLin s (w0At m s) := HLall.hw0At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_w0At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
    have hs : row0Sigma s (w0At m s) = 0 := H.hw0AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := w0At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := w0At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_w0At_fromHeart
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s s.ρ (w0At m s) := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  exact row012ConvolutionAtRev_w0At_fromHeart_of_coords
    (m := m) (s := s) HC

/-- Build Row012ConvolutionAtRev for `wp2At m s` using heart constraints + Route-A witnesses. -/
theorem row012ConvolutionAtRev_wp2At_fromHeart_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (HC : XiAtOrderCoords01Out m s) :
    Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromHeart_of_coords (m := m) (s := s) HC
  have HL : Row012ExtraLin s (wp2At m s) := HLall.hwp2At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp2At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
    have hs : row0Sigma s (wp2At m s) = 0 := H.hwp2AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp2At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp2At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp2At_fromHeart
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  exact row012ConvolutionAtRev_wp2At_fromHeart_of_coords
    (m := m) (s := s) HC

/-- Build Row012ConvolutionAtRev for `wp3At m s` using heart constraints + Route-A witnesses. -/
theorem row012ConvolutionAtRev_wp3At_fromHeart_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (HC : XiAtOrderCoords01Out m s) :
    Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromHeart_of_coords (m := m) (s := s) HC
  have HL : Row012ExtraLin s (wp3At m s) := HLall.hwp3At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp3At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
    have hs : row0Sigma s (wp3At m s) = 0 := H.hwp3AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp3At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp3At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp3At_fromHeart
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  exact row012ConvolutionAtRev_wp3At_fromHeart_of_coords
    (m := m) (s := s) HC

/-- Final discharge: build the AtOrder Row012 bundle from an explicit coords payload. -/
theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (HC : XiAtOrderCoords01Out m s) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row012ConvolutionAtRev_w0At_fromHeart_of_coords (m := m) (s := s) HC
  · exact row012ConvolutionAtRev_wp2At_fromHeart_of_coords (m := m) (s := s) HC
  · exact row012ConvolutionAtRev_wp3At_fromHeart_of_coords (m := m) (s := s) HC

/-- Final discharge: build the AtOrder Row012 bundle. -/
theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] [A0Nonzero (s := s)]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  exact xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_discharge_of_coords
    (m := m) (s := s) HC

end XiPacket
end Targets
end Hyperlocal
