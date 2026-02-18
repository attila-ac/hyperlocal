/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizToConvolution.lean

  Convert the Route-L semantic payload `JetLeibnizAt` into a genuine
  Cauchy-product `Convolution` statement.

  IMPORTANT (correct scaling):
  A plain Cauchy product matches *power-series coefficients*, i.e. derivatives
  divided by factorials. Therefore we encode 2-jets using the scaled entries

    f₀ = f
    f₁ = f'
    f₂ = f'' / 2

  so that the Cauchy coefficient at n=2 matches the Leibniz binomial factor `2`.

  Support:
  both scaled sequences are supported in degrees ≤ 2, so the Cauchy product is
  supported in degrees ≤ 4; hence coefficients are definitional 0 only for n ≥ 5.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Cancellation.Recurrence
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

/-- Jet of `Rfun s` at `z` as a padded **scaled** coefficient sequence (0,1,2 with /2). -/
def rJetSeq (s : OffSeed Xi) (z : ℂ) : ℕ → ℂ
  | 0 => (Rfun s) z
  | 1 => deriv (Rfun s) z
  | 2 => deriv (deriv (Rfun s)) z / (2 : ℂ)
  | _ => 0

/-- Padded **scaled** window coefficient sequence (w0,w1,w2 with /2). -/
def wJetSeq (w : Transport.Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2 / (2 : ℂ)
  | _ => 0

/--
Target sequence for the convolution statement.

* At n = 0,1,2: the **scaled** `Xi` jet values (0,1,2 with /2).
* At n = 3,4: defined to be the Cauchy coefficients (so convolution holds by rfl).
* At n ≥ 5: zero (and the Cauchy coefficients are provably zero by support).
-/
def xiJetSeq (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : ℕ → ℂ
  | 0 => Xi z
  | 1 => deriv Xi z
  | 2 => deriv (deriv Xi) z / (2 : ℂ)
  | 3 => convCoeff (rJetSeq s z) (wJetSeq w) 3
  | 4 => convCoeff (rJetSeq s z) (wJetSeq w) 4
  | _ => 0

/-- Support: `rJetSeq` vanishes for indices ≥ 3. -/
lemma rJetSeq_eq_zero_of_ge3 (s : OffSeed Xi) (z : ℂ) :
    ∀ k : ℕ, 3 ≤ k → rJetSeq s z k = 0 := by
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
              simp [rJetSeq]

/-- Support: `wJetSeq` vanishes for indices ≥ 3. -/
lemma wJetSeq_eq_zero_of_ge3 (w : Transport.Window 3) :
    ∀ k : ℕ, 3 ≤ k → wJetSeq w k = 0 := by
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
              simp [wJetSeq]

/-- Support lemma: coefficients vanish for n ≥ 5. -/
lemma convCoeff_rJetSeq_wJetSeq_ge5 (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    ∀ n, convCoeff (rJetSeq s z) (wJetSeq w) (n + 5) = 0 := by
  intro n
  classical
  simp [convCoeff]
  refine Finset.sum_eq_zero ?_
  intro x hx
  by_cases hx3 : 3 ≤ x
  ·
    have hx0 : rJetSeq s z x = 0 := rJetSeq_eq_zero_of_ge3 (s := s) (z := z) x hx3
    simp [hx0]
  ·
    -- FIX: we need x ≤ 2 from ¬(3 ≤ x), not from a mismatched `Nat.le_of_not_ge`.
    have hxle : x ≤ 2 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hx3)
    have hsub : (n + 5) - 2 ≤ (n + 5) - x :=
      Nat.sub_le_sub_left hxle (n + 5)
    have hge3 : 3 ≤ (n + 5) - 2 := by
      -- (n+5)-2 = n+3
      simpa using (Nat.le_add_left 3 n)
    have hge3' : 3 ≤ (n + 5) - x := le_trans (by simpa using hge3) hsub
    have hy0 : wJetSeq w ((n + 5) - x) = 0 :=
      wJetSeq_eq_zero_of_ge3 (w := w) ((n + 5) - x) hge3'
    simp [hy0]

/--
Main theorem: `JetLeibnizAt` implies the convolution statement
`Convolution (rJetSeq s z) (wJetSeq w) (xiJetSeq s z w)`.
-/
theorem convolution_of_JetLeibnizAt
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetLeibnizAt s z w →
      Convolution (rJetSeq s z) (wJetSeq w) (xiJetSeq s z w) := by
  intro hL
  classical
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  intro n
  cases n with
  | zero =>
      simpa [xiJetSeq, convCoeff, rJetSeq, wJetSeq] using h0.symm
  | succ n =>
      cases n with
      | zero =>
          simpa [xiJetSeq, convCoeff, rJetSeq, wJetSeq, Finset.range_succ,
                add_comm, add_left_comm, add_assoc] using h1.symm
      | succ n =>
          cases n with
          | zero =>
              have hc2 :
                  convCoeff (rJetSeq s z) (wJetSeq w) 2 =
                    deriv (deriv (Rfun s)) z / (2 : ℂ) * (w 0)
                      + deriv (Rfun s) z * (w 1)
                      + (Rfun s) z * (w 2 / (2 : ℂ)) := by
                simp [convCoeff, rJetSeq, wJetSeq, Finset.range_succ]
                ring_nf
              have h2scaled :
                  deriv (deriv Xi) z / (2 : ℂ) =
                    deriv (deriv (Rfun s)) z / (2 : ℂ) * (w 0)
                      + deriv (Rfun s) z * (w 1)
                      + (Rfun s) z * (w 2 / (2 : ℂ)) := by
                calc
                  deriv (deriv Xi) z / (2 : ℂ)
                      = (deriv (deriv (Rfun s)) z * (w 0)
                          + (2 : ℂ) * (deriv (Rfun s) z) * (w 1)
                          + (Rfun s) z * (w 2)) / (2 : ℂ) := by
                            simpa [h2]
                  _   = deriv (deriv (Rfun s)) z / (2 : ℂ) * (w 0)
                          + deriv (Rfun s) z * (w 1)
                          + (Rfun s) z * (w 2 / (2 : ℂ)) := by
                            ring_nf
              have : convCoeff (rJetSeq s z) (wJetSeq w) 2 = deriv (deriv Xi) z / (2 : ℂ) := by
                exact (hc2.trans (by simpa using h2scaled.symm))
              simpa [xiJetSeq] using this
          | succ n =>
              cases n with
              | zero =>
                  simp [xiJetSeq]
              | succ n =>
                  cases n with
                  | zero =>
                      simp [xiJetSeq]
                  | succ n =>
                      have hc :
                          convCoeff (rJetSeq s z) (wJetSeq w)
                            (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))) = 0 := by
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                          convCoeff_rJetSeq_wJetSeq_ge5 (s := s) (z := z) (w := w) n
                      simpa [xiJetSeq] using hc

end XiPacket
end Targets
end Hyperlocal
