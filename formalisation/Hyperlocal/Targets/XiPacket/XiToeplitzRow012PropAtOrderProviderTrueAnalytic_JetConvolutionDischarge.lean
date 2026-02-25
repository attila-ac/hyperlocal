/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge.lean

  REAL analytic discharge surface (manuscript-facing), Lean-28 style:

  Goal:
    instance : XiJetConvolutionAtRevAtOrderTrueAnalytic

  Key observation (crucial):
  For the reverse convolution used in `JetConvolutionAtRev`:

    convCoeff (row0CoeffSeqRev s) (winSeqRev w) n

  the sequences are FINITELY SUPPORTED:
    * row0CoeffSeqRev s k = 0 for k ≥ 4
    * winSeqRev w k       = 0 for k ≥ 3

  Therefore convCoeff(...) n = 0 holds definitional-by-support for all n ≥ 6.
  So the only nontrivial analytic obligations are exactly n = 3,4,5.

  We isolate those as a tiny Prop-gate:
      [XiJetConvolutionTail345AtOrderTrueAnalytic]

  Then we build `JetConvolutionAtRev` (which asks ∀ n ≥ 3) by:
    * cases n=3,4,5 using the gate
    * n ≥ 6 using support.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA

-- needed for `Hyperlocal.Cancellation.convCoeff`
import Hyperlocal.Cancellation.Recurrence

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Manuscript-facing analytic tail gate (ONLY the real obligations):

Provide the reverse-Cauchy coefficient vanishings at n = 3,4,5
for the three canonical AtOrder windows.
-/
class XiJetConvolutionTail345AtOrderTrueAnalytic : Prop where
  tail3_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
  tail4_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0
  tail5_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0

  tail3_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
  tail4_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0
  tail5_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0

  tail3_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0
  tail4_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0
  tail5_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0

/-- Support: winSeqRev vanishes for indices ≥ 3. -/
lemma winSeqRev_eq_zero_of_ge3 (w : Transport.Window 3) :
    ∀ k : ℕ, 3 ≤ k → winSeqRev w k = 0 := by
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

/-- Support: row0CoeffSeqRev vanishes for indices ≥ 4. -/
lemma row0CoeffSeqRev_eq_zero_of_ge4 (s : OffSeed Xi) :
    ∀ k : ℕ, 4 ≤ k → row0CoeffSeqRev s k = 0 := by
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
Pure support lemma: coefficients vanish for n ≥ 6.

Because row0CoeffSeqRev has support ≤ 3 and winSeqRev has support ≤ 2,
their Cauchy coefficient at n = 6 + t is zero by support.
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
    have hx0 : row0CoeffSeqRev s x = 0 := row0CoeffSeqRev_eq_zero_of_ge4 (s := s) x hx4
    simp [hx0]
  ·
    -- x ≤ 3
    have hxlt : x < 4 := Nat.lt_of_not_ge hx4
    have hxle : x ≤ 3 := Nat.le_of_lt_succ (by simpa using hxlt)
    have hsub : (t + 6) - 3 ≤ (t + 6) - x :=
      Nat.sub_le_sub_left hxle (t + 6)
    have hge3 : 3 ≤ (t + 6) - 3 := by
      -- (t+6)-3 = t+3
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.le_add_left 3 t)
    have hge3' : 3 ≤ (t + 6) - x := le_trans (by simpa using hge3) hsub
    have hy0 : winSeqRev w ((t + 6) - x) = 0 :=
      winSeqRev_eq_zero_of_ge3 (w := w) ((t + 6) - x) hge3'
    simp [hy0]

namespace JetQuotOp

/--
Build the full tail predicate ∀ n ≥ 3 from:
  * the three real obligations at 3/4/5, and
  * support for n ≥ 6.
-/
private lemma tail_from_345
    (s : OffSeed Xi) (w : Transport.Window 3)
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0)
    (h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0)
    (h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0) :
    ∀ n, 3 ≤ n → convCoeff (row0CoeffSeqRev s) (winSeqRev w) n = 0 := by
  intro n hn
  -- brute-force case split up to 5; beyond that, use support.
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
              -- now original n is 3 + n
              cases n with
              | zero =>
                  simpa using h3
              | succ n =>
                  -- original is 4 + n
                  cases n with
                  | zero =>
                      simpa using h4
                  | succ n =>
                      -- original is 5 + n
                      cases n with
                      | zero =>
                          simpa using h5
                      | succ n =>
                          -- original is 6 + n
                          have : convCoeff (row0CoeffSeqRev s) (winSeqRev w) (n + 6) = 0 :=
                            convCoeff_row0CoeffSeqRev_winSeqRev_ge6 (s := s) (w := w) n
                          -- rewrite (n+6) into the current numeral form
                          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Route–A package + tail(3/4/5) ⇒ `JetConvolutionAtRev` for `w0At`. -/
theorem jetConvRev_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiJetConvolutionTail345AtOrderTrueAnalytic] :
    JetConvolutionAtRev s s.ρ (w0At m s) := by
  classical
  rcases xiRouteA_jetPkg_w0At (m := m) (s := s) with
    ⟨G, hfac, hjet, _hR, _hG, _hR', _hG'⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_w0At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_w0At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_w0At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := w0At m s) h3 h4 h5

/-- Route–A package + tail(3/4/5) ⇒ `JetConvolutionAtRev` for `wp2At`. -/
theorem jetConvRev_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiJetConvolutionTail345AtOrderTrueAnalytic] :
    JetConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  rcases xiRouteA_jetPkg_wp2At (m := m) (s := s) with
    ⟨G, hfac, hjet, _hR, _hG, _hR', _hG'⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_wp2At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_wp2At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_wp2At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := wp2At m s) h3 h4 h5

/-- Route–A package + tail(3/4/5) ⇒ `JetConvolutionAtRev` for `wp3At`. -/
theorem jetConvRev_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiJetConvolutionTail345AtOrderTrueAnalytic] :
    JetConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  rcases xiRouteA_jetPkg_wp3At (m := m) (s := s) with
    ⟨G, hfac, hjet, _hR, _hG, _hR', _hG'⟩
  have h3 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail3_wp3At (m := m) (s := s)
  have h4 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail4_wp3At (m := m) (s := s)
  have h5 := XiJetConvolutionTail345AtOrderTrueAnalytic.tail5_wp3At (m := m) (s := s)
  refine ⟨G, hfac, hjet, ?_⟩
  exact tail_from_345 (s := s) (w := wp3At m s) h3 h4 h5

end JetQuotOp

/--
Main milestone: once the manuscript discharges ONLY the (3,4,5) tail gate,
we get the full `JetConvolutionAtRev` Prop-gate for free.
-/
instance (priority := 1000)
    [XiJetConvolutionTail345AtOrderTrueAnalytic] :
    XiJetConvolutionAtRevAtOrderTrueAnalytic where
  jet_w0At  := by intro m s; exact JetQuotOp.jetConvRev_w0At_trueAnalytic (m := m) (s := s)
  jet_wp2At := by intro m s; exact JetQuotOp.jetConvRev_wp2At_trueAnalytic (m := m) (s := s)
  jet_wp3At := by intro m s; exact JetQuotOp.jetConvRev_wp3At_trueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
