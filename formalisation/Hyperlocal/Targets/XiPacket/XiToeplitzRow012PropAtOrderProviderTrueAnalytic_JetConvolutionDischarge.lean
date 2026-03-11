/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge.lean

  REAL analytic discharge surface (manuscript-facing), Lean-28 style:

  Goal:
    instance : XiJetConvolutionAtRevAtOrderTrueAnalytic

  This file uses ONLY the tail gate interface:
    [XiJetConvolutionTail345AtOrderTrueAnalytic]

  2026-03-11:
  Retargeted from the legacy ambient Route-A Leibniz wrapper to the
  theorem-side wrapper with explicit gate
    [TAC.XiJetWindowEqAtOrderQuotProvider].
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem

-- tail gate interface (cycle-safe)
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Interface

-- needed for `Hyperlocal.Cancellation.convCoeff`
import Hyperlocal.Cancellation.Recurrence

import Mathlib.Tactic

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

/-- Support: winSeqRev vanishes for indices >= 3. -/
lemma winSeqRev_eq_zero_of_ge3 (w : Transport.Window 3) :
    ∀ k : ℕ, 3 ≤ k -> winSeqRev w k = 0 := by
  intro k hk
  cases k with
  | zero =>
      exact (False.elim (Nat.not_succ_le_zero 2 hk))
  | succ k =>
      cases k with
      | zero =>
          exact (False.elim (by simpa using hk))
      | succ k =>
          cases k with
          | zero =>
              exact (False.elim (by simpa using hk))
          | succ k =>
              simp [winSeqRev]

/-- Support: row0CoeffSeqRev vanishes for indices >= 4. -/
lemma row0CoeffSeqRev_eq_zero_of_ge4 (s : OffSeed Xi) :
    ∀ k : ℕ, 4 ≤ k -> row0CoeffSeqRev s k = 0 := by
  intro k hk
  cases k with
  | zero =>
      exact (False.elim (Nat.not_succ_le_zero 3 hk))
  | succ k =>
      cases k with
      | zero =>
          exact (False.elim (by simpa using hk))
      | succ k =>
          cases k with
          | zero =>
              exact (False.elim (by simpa using hk))
          | succ k =>
              cases k with
              | zero =>
                  exact (False.elim (by simpa using hk))
              | succ k =>
                  simp [row0CoeffSeqRev]

/--
Pure support lemma: coefficients vanish for n >= 6.
-/
lemma convCoeff_row0CoeffSeqRev_winSeqRev_ge6
    (s : OffSeed Xi) (w : Transport.Window 3) :
    ∀ t : ℕ, convCoeff (row0CoeffSeqRev s) (winSeqRev w) (t + 6) = 0 := by
  intro t
  classical
  simp [convCoeff]
  refine Finset.sum_eq_zero ?_
  intro x hx
  by_cases hx4 : 4 ≤ x
  ·
    have hx0 : row0CoeffSeqRev s x = 0 :=
      row0CoeffSeqRev_eq_zero_of_ge4 (s := s) x hx4
    simp [hx0]
  ·
    have hxlt : x < 4 := Nat.lt_of_not_ge hx4
    have hxle : x ≤ 3 := Nat.le_of_lt_succ (by simpa using hxlt)
    have hsub : (t + 6) - 3 ≤ (t + 6) - x :=
      Nat.sub_le_sub_left hxle (t + 6)
    have hge3 : 3 ≤ (t + 6) - 3 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.le_add_left 3 t)
    have hge3' : 3 ≤ (t + 6) - x := le_trans (by simpa using hge3) hsub
    have hy0 : winSeqRev w ((t + 6) - x) = 0 :=
      winSeqRev_eq_zero_of_ge3 (w := w) ((t + 6) - x) hge3'
    simp [hy0]

namespace JetQuotOp

private lemma tail_from_345
    (s : OffSeed Xi) (w : Transport.Window 3)
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0)
    (h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0)
    (h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0) :
    ∀ n, 3 ≤ n -> convCoeff (row0CoeffSeqRev s) (winSeqRev w) n = 0 := by
  intro n hn
  cases n with
  | zero =>
      exact (False.elim (Nat.not_succ_le_zero 2 hn))
  | succ n =>
      cases n with
      | zero =>
          exact (False.elim (by simpa using hn))
      | succ n =>
          cases n with
          | zero =>
              exact (False.elim (by simpa using hn))
          | succ n =>
              cases n with
              | zero => simpa using h3
              | succ n =>
                  cases n with
                  | zero => simpa using h4
                  | succ n =>
                      cases n with
                      | zero => simpa using h5
                      | succ n =>
                          have : convCoeff (row0CoeffSeqRev s) (winSeqRev w) (n + 6) = 0 :=
                            convCoeff_row0CoeffSeqRev_winSeqRev_ge6 (s := s) (w := w) n
                          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem jetConvRev_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetConvolutionTail345AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetConvolutionAtRev s s.ρ (w0At m s) := by
  classical
  rcases JetQuotOpTheorem.xiRouteA_jetPkg_w0At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_w0At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_w0At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_w0At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := w0At m s) h3 h4 h5

theorem jetConvRev_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetConvolutionTail345AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp2At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_wp2At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_wp2At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_wp2At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := wp2At m s) h3 h4 h5

theorem jetConvRev_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetConvolutionTail345AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp3At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_wp3At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_wp3At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_wp3At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := wp3At m s) h3 h4 h5

end JetQuotOp

instance (priority := 1000)
    [XiJetConvolutionTail345AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetConvolutionAtRevAtOrderTrueAnalytic where
  jet_w0At := by
    intro m s
    exact JetQuotOp.jetConvRev_w0At_trueAnalytic (m := m) (s := s)
  jet_wp2At := by
    intro m s
    exact JetQuotOp.jetConvRev_wp2At_trueAnalytic (m := m) (s := s)
  jet_wp3At := by
    intro m s
    exact JetQuotOp.jetConvRev_wp3At_trueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
