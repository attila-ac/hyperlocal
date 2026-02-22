/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_EvalGerm.lean

  Step 1 of the "J3 analytic discharge playbook":

    Define a J3-evaluation semantics for an analytic germ given by its (formal) Taylor
    coefficients a : ℕ → ℂ at an anchor, evaluated at the nilpotent shift u(δ) = C δ + w.

  Key point: evaluation is defined for *finite* truncations in the Taylor index n,
  and we prove an exact reduction to degrees 0,1,2 in the nilpotent direction w.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_Binomial
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex
open scoped BigOperators

namespace J3

/-- Avoid `[simp]` here: it can loop via coercions/`map_natCast`. -/
lemma natCast_eq_C (n : ℕ) : (n : J3) = C (n : ℂ) := by
  exact (map_natCast C n).symm

/-- The finite-n truncation of a germ evaluated at the shift element `u(δ) = C δ + w`. -/
def evalTrunc (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) : J3 :=
  (Finset.range N).sum (fun n => (C (a n)) * (uδ δ) ^ n)

/-- The k-th coefficient (k=0,1,2) appearing after reducing modulo `w^3`. -/
def coeff (a : ℕ → ℂ) (δ : ℂ) (N k : ℕ) : ℂ :=
  (Finset.range N).sum (fun n => a n * (Nat.choose n k : ℂ) * δ ^ (n - k))

@[simp] lemma coeff_def (a : ℕ → ℂ) (δ : ℂ) (N k : ℕ) :
    coeff a δ N k =
      (Finset.range N).sum (fun n => a n * (Nat.choose n k : ℂ) * δ ^ (n - k)) :=
  rfl

/-- Controlled “push into `C`” for one summand (NO simp/simpa). -/
lemma push_C_summand (a : ℂ) (δ : ℂ) (n k : ℕ) :
    (C a) * ((Nat.choose n k : J3) * (C δ) ^ (n - k))
      =
    C (a * (Nat.choose n k : ℂ) * δ ^ (n - k)) := by
  have hchoose : (Nat.choose n k : J3) = C (Nat.choose n k : ℂ) := by
    exact (map_natCast C (Nat.choose n k)).symm
  have hpow : (C δ) ^ (n - k) = C (δ ^ (n - k)) := by
    exact (map_pow C δ (n - k)).symm
  rw [hchoose, hpow]

  have hinner :
      (C (Nat.choose n k : ℂ)) * (C (δ ^ (n - k)))
        =
      C ((Nat.choose n k : ℂ) * (δ ^ (n - k))) := by
    exact (map_mul C (Nat.choose n k : ℂ) (δ ^ (n - k))).symm

  calc
    (C a) * (C (Nat.choose n k : ℂ) * C (δ ^ (n - k)))
        =
      (C a) * ((C (Nat.choose n k : ℂ)) * (C (δ ^ (n - k)))) := by
        ac_rfl
    _ =
      (C a) * C ((Nat.choose n k : ℂ) * (δ ^ (n - k))) := by
        rw [hinner]
    _ =
      C (a * ((Nat.choose n k : ℂ) * (δ ^ (n - k)))) := by
        exact (map_mul C a ((Nat.choose n k : ℂ) * (δ ^ (n - k)))).symm
    _ =
      C (a * (Nat.choose n k : ℂ) * δ ^ (n - k)) := by
        ac_rfl

/--
Core reduction lemma: truncation in the Taylor index collapses exactly to degrees ≤ 2 in w.
-/
theorem evalTrunc_eq_sum_wdeg_two (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) :
    evalTrunc a δ N
      =
    (Finset.range 3).sum (fun k => (C (coeff a δ N k)) * (w : J3) ^ k) := by
  classical

  -- Expand `(uδ δ)^n` via truncated binomial.
  have hexpand :
      evalTrunc a δ N
        =
      (Finset.range N).sum (fun n =>
        (C (a n)) *
          (Finset.range 3).sum (fun k =>
            (Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k)) := by
    unfold evalTrunc
    refine Finset.sum_congr rfl ?_
    intro n hn
    simpa using congrArg (fun t => (C (a n)) * t)
      (u_pow_eq_sum_choose_range_three (δ := δ) (n := n))

  rw [hexpand]

  -- Distribute `C(a n)` across the inner sum without `Finset.mul_sum`
  -- (some snapshots have argument order issues / different lemma names).
  have hdist :
      (Finset.range N).sum (fun n =>
          (C (a n)) *
            (Finset.range 3).sum (fun k =>
              (Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k))
        =
      (Finset.range N).sum (fun n =>
          (Finset.range 3).sum (fun k =>
            (C (a n)) *
              ((Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k))) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    let g : ℕ → J3 := fun k =>
      (Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k
    calc
      (C (a n)) * (Finset.range 3).sum g
          = ((Finset.range 3).sum g) * (C (a n)) := by
              ac_rfl
      _   = (Finset.range 3).sum (fun k => g k * (C (a n))) := by
              exact (Finset.sum_mul (Finset.range 3) g (C (a n)))
      _   = (Finset.range 3).sum (fun k => (C (a n)) * g k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ac_rfl
      _   = (Finset.range 3).sum (fun k =>
              (C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k)) := by
              rfl

  rw [hdist]

  -- Commute the finite sums.
  rw [Finset.sum_comm]

  -- Work pointwise in k.
  refine Finset.sum_congr rfl ?_
  intro k hk

  -- Reassociate to expose right-multiplication by w^k.
  have hreassoc :
      (Finset.range N).sum (fun n =>
          (C (a n)) *
            ((Nat.choose n k : J3) * (C δ) ^ (n - k) * (w : J3) ^ k))
        =
      (Finset.range N).sum (fun n =>
          ((C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k))) * (w : J3) ^ k) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    ac_rfl

  rw [hreassoc]

  -- Factor out w^k on the right.
  have hfactor :
      (Finset.range N).sum (fun n =>
          ((C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k))) * (w : J3) ^ k)
        =
      ((Finset.range N).sum (fun n =>
          (C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k))))
        * (w : J3) ^ k := by
    exact (Finset.sum_mul (Finset.range N)
      (fun n => (C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k)))
      ((w : J3) ^ k)).symm

  rw [hfactor]

  -- Identify coefficient sum as `C (coeff ...)`.
  have hcoeff :
      (Finset.range N).sum (fun n =>
          (C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k)))
        =
      C (coeff a δ N k) := by
    unfold coeff
    have hsummand :
        (fun n =>
            (C (a n)) * ((Nat.choose n k : J3) * (C δ) ^ (n - k)))
          =
        (fun n =>
            C (a n * (Nat.choose n k : ℂ) * δ ^ (n - k))) := by
      funext n
      exact push_C_summand (a := a n) (δ := δ) (n := n) (k := k)
    rw [hsummand]
    exact (map_sum C (fun n => a n * (Nat.choose n k : ℂ) * δ ^ (n - k)) (Finset.range N)).symm

  rw [hcoeff]

end J3

end TAC
end XiPacket
end Targets
end Hyperlocal
