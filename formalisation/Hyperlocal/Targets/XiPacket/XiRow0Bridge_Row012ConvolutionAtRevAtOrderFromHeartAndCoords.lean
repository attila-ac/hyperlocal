/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromHeartAndCoords.lean

  Cycle-safe core builder:
    heart bundle + coords01 bundle  ==>  Row012 reverse-stencil payload.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Core builder: heart + coords ⇒ row012 reverse-stencil payload (AtOrder). -/
theorem xiRow012ConvolutionAtRevAtOrderOut_of_heart_and_coords
    (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotRow0AtOrderHeartOut m s)
    (HC : XiAtOrderCoords01Out m s) :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  classical
  refine ⟨?_, ?_, ?_⟩

  · -- w0At
    rcases JetQuotOp.xiRouteA_jetPkg_w0At (m := m) (s := s) with
      ⟨G, hfac, hjet, _, _, _, _⟩
    have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
      have hs : row0Sigma s (w0At m s) = 0 := H.hw0AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs
    have H0 : Row0ConvolutionAtRev s (s.ρ) (w0At m s) := ⟨G, hfac, hjet, h3⟩
    have HL : Row012ExtraLin s (w0At m s) :=
      row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1
    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
      (s := s) (z := s.ρ) (w := w0At m s) H0 HL

  · -- wp2At
    rcases JetQuotOp.xiRouteA_jetPkg_wp2At (m := m) (s := s) with
      ⟨G, hfac, hjet, _, _, _, _⟩
    have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
      have hs : row0Sigma s (wp2At m s) = 0 := H.hwp2AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs
    have H0 : Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := ⟨G, hfac, hjet, h3⟩
    have HL : Row012ExtraLin s (wp2At m s) :=
      row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1
    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) H0 HL

  · -- wp3At
    rcases JetQuotOp.xiRouteA_jetPkg_wp3At (m := m) (s := s) with
      ⟨G, hfac, hjet, _, _, _, _⟩
    have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
      have hs : row0Sigma s (wp3At m s) = 0 := H.hwp3AtSigma
      simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs
    have H0 : Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := ⟨G, hfac, hjet, h3⟩
    have HL : Row012ExtraLin s (wp3At m s) :=
      row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1
    exact row012ConvolutionAtRev_of_row0ConvolutionAtRev_and_extraLin
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) H0 HL

end XiPacket
end Targets
end Hyperlocal
