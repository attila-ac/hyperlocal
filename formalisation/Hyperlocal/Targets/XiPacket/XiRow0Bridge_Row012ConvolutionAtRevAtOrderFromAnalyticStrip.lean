/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalyticStrip.lean

  Non-cycle-safe strip wrapper for the Row012 reverse-stencil payload at order m,
  without importing the global nondegeneracy axiom module.

  This file is allowed to import the strip heart + strip coords export layers.
-/

import Hyperlocal.Transport.OffSeedStrip

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticStrip

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionFromRow0AndCoords
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Strip-specialised discharged Row012 reverse-stencil payload (AtOrder). -/
theorem xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiRow012ConvolutionAtRevAtOrderOut m (s : OffSeed Xi) := by
  classical
  set s0 : OffSeed Xi := (s : OffSeed Xi)

  have Hheart : XiJetQuotRow0AtOrderHeartOut m s0 :=
    xiJetQuotRow0AtOrderHeartOut_fromAnalytic_strip (m := m) (s := s)
  have Hcoords : XiAtOrderCoords01Out m s0 :=
    xiAtOrderCoords01Out_fromAnalytic_strip (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩

  · -- w0At
    rcases JetQuotOp.xiRouteA_jetPkg (s := s0) (z := s0.ρ) (w := w0At m s0) with
      ⟨G, hfac, hjet, _, _, _, _⟩

    have h3 : convCoeff (row0CoeffSeqRev s0) (winSeqRev (w0At m s0)) 3 = 0 := by
      have hs : row0Sigma s0 (w0At m s0) = 0 := Hheart.hw0AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s0) (w := w0At m s0)] using hs

    have H0 : Row0ConvolutionAtRev s0 (s0.ρ) (w0At m s0) :=
      ⟨G, hfac, hjet, h3⟩

    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_coords
      (s := s0) (z := s0.ρ) (w := w0At m s0)
      H0 Hcoords.hw0At0 Hcoords.hw0At1

  · -- wp2At
    rcases JetQuotOp.xiRouteA_jetPkg
        (s := s0) (z := (starRingEnd ℂ) s0.ρ) (w := wp2At m s0) with
      ⟨G, hfac, hjet, _, _, _, _⟩

    have h3 : convCoeff (row0CoeffSeqRev s0) (winSeqRev (wp2At m s0)) 3 = 0 := by
      have hs : row0Sigma s0 (wp2At m s0) = 0 := Hheart.hwp2AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s0) (w := wp2At m s0)] using hs

    have H0 : Row0ConvolutionAtRev s0 ((starRingEnd ℂ) s0.ρ) (wp2At m s0) :=
      ⟨G, hfac, hjet, h3⟩

    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_coords
      (s := s0) (z := (starRingEnd ℂ) s0.ρ) (w := wp2At m s0)
      H0 Hcoords.hwp2At0 Hcoords.hwp2At1

  · -- wp3At
    rcases JetQuotOp.xiRouteA_jetPkg
        (s := s0) (z := (1 - (starRingEnd ℂ) s0.ρ)) (w := wp3At m s0) with
      ⟨G, hfac, hjet, _, _, _, _⟩

    have h3 : convCoeff (row0CoeffSeqRev s0) (winSeqRev (wp3At m s0)) 3 = 0 := by
      have hs : row0Sigma s0 (wp3At m s0) = 0 := Hheart.hwp3AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s0) (w := wp3At m s0)] using hs

    have H0 : Row0ConvolutionAtRev s0 (1 - (starRingEnd ℂ) s0.ρ) (wp3At m s0) :=
      ⟨G, hfac, hjet, h3⟩

    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_coords
      (s := s0) (z := (1 - (starRingEnd ℂ) s0.ρ)) (w := wp3At m s0)
      H0 Hcoords.hwp3At0 Hcoords.hwp3At1

end XiPacket
end Targets
end Hyperlocal
