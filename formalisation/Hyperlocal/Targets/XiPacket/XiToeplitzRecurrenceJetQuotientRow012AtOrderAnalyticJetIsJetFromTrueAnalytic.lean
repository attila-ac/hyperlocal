/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetFromTrueAnalytic.lean

  Goal:
    Prove the three jet predicates from the true-analytic Row012 payload.

  This file contains NO axioms.
  Any remaining gaps should appear as `sorry` (local analytic TODO),
  not as global axioms.

  Strategy:
  * Pull the analytic Row012 reverse-convolution payload:
      Hst : XiRow012ConvolutionAtRevAtOrderOut m s
  * Each field (hw0At/hwp2At/hwp3At) is a Row012 reverse-convolution statement,
    packaging a witness G and a jet fact IsJet3At G z w plus convolution constraints.
  * The remaining analytic cliff is to identify that witness G with
      cderivIter m Xi
    (up to 2nd derivative at the anchor), upgrading the jet to IsJet3AtOrder.

  All remaining analytic work is localized in:
      isJet3AtOrder_of_row012ConvolutionAtRev
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-
  Anchor sanity:

  The Row012 payload uses anchors:
    hw0At  at z = s.ρ
    hwp2At at z = star s.ρ
    hwp3At at z = 1 - star s.ρ

  Our abbreviations:
    z_w0At  s := sc s + (delta s : ℝ)
    z_wp2At s := star s.ρ
    z_wp3At s := 1 - star s.ρ

  Only non-definitional alignment is `z_w0At s = s.ρ`.
-/
private lemma z_w0At_eq_rho (s : OffSeed Xi) : z_w0At s = s.ρ := by
  -- expand defs: sc s = (1/2) + I*(t s), delta s = (σ s - 1/2)
  -- so sc+delta = (σ s) + I*(t s) = s.ρ
  refine Complex.ext ?_ ?_
  · -- real parts
    -- `simp` should reduce `re` of complex additions and real-casts
    simp [z_w0At, XiTransport.delta, sc, σ, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · -- imaginary parts
    simp [z_w0At, XiTransport.delta, sc, σ, t, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-
  Core reduction lemma (the single analytic cliff):

  From `Row012ConvolutionAtRev s z w`, you get:
    ∃ G, FactorisedByQuartet ... G ∧ IsJet3At G z w ∧ (conv constraints)

  To upgrade to `IsJet3AtOrder m z w` (i.e. IsJet3At (cderivIter m Xi) z w),
  you must identify that witness `G` with `cderivIter m Xi` at `z`
  at least up to second derivative.
-/
private theorem isJet3AtOrder_of_row012ConvolutionAtRev
    (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    IsJet3AtOrder m z w := by
  classical
  rcases H with ⟨G, hfac, hjet, h3, h4, h5⟩
  -- hfac : FactorisedByQuartet Xi s.ρ 1 G
  -- hjet : IsJet3At G z w
  -- h3,h4,h5 : row012 reverse convolution constraints

  -- Goal is:
  --   IsJet3At (cderivIter m Xi) z w
  --
  -- TODO (analytic identification):
  --   Prove that `G` agrees with `cderivIter m Xi` at `z` up to 2nd derivative,
  --   using your FE/RC/factorisation identification layer (Route-A / manuscript),
  --   then rewrite `hjet`.
  --
  -- This is the *only* remaining analytic cliff in this file.
  sorry

/-- Target 1: w0At is an order-m jet at z_w0At. -/
theorem jet_w0At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

  -- Payload gives `Row012ConvolutionAtRev s s.ρ (w0At m s)`.
  -- Rewrite anchor to `z_w0At s`.
  have H : Row012ConvolutionAtRev s (z_w0At s) (w0At m s) := by
    simpa [z_w0At_eq_rho (s := s)] using Hst.hw0At

  exact isJet3AtOrder_of_row012ConvolutionAtRev
    (m := m) (s := s) (z := z_w0At s) (w := w0At m s) H

/-- Target 2: wp2At jet. -/
theorem jet_wp2At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

  -- Here the anchor matches definitionally.
  have H : Row012ConvolutionAtRev s (z_wp2At s) (wp2At m s) := by
    simpa [z_wp2At] using Hst.hwp2At

  exact isJet3AtOrder_of_row012ConvolutionAtRev
    (m := m) (s := s) (z := z_wp2At s) (w := wp2At m s) H

/-- Target 3: wp3At jet. -/
theorem jet_wp3At_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

  -- Here the anchor matches definitionally.
  have H : Row012ConvolutionAtRev s (z_wp3At s) (wp3At m s) := by
    simpa [z_wp3At] using Hst.hwp3At

  exact isJet3AtOrder_of_row012ConvolutionAtRev
    (m := m) (s := s) (z := z_wp3At s) (w := wp3At m s) H

/--
Once the three jet theorems are proved, install the provider.
-/
instance : XiJetWindowIsJetAtOrderProvider where
  jet_w0At  := jet_w0At_fromTrueAnalytic
  jet_wp2At := jet_wp2At_fromTrueAnalytic
  jet_wp3At := jet_wp3At_fromTrueAnalytic

end TAC

end XiPacket
end Targets
end Hyperlocal
