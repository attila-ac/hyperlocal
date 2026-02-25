/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Reductions.lean

  Pure-algebra reductions for the ONLY analytic obligations:

    convCoeff (row0CoeffSeqRev s) (winSeqRev (w?At m s)) n = 0
  for n = 3,4,5 and w?At ∈ {w0At, wp2At, wp3At}.

  Snapshot-robust rule:
  * DO NOT `simp` a hypothesis of the form `convCoeff ... = 0`
    because this snapshot eagerly unfolds `convCoeff` into `Finset.sum`.
  * Instead, shuttle between closed forms using `calc` with `hEq` / `Eq.symm hEq`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff345Algebra
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

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

namespace Tail345Reductions

/-- Generic reduction at n=3: `convCoeff ... 3 = 0` ↔ `row0Sigma = 0`. -/
theorem tail3_iff_row0Sigma
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0
      ↔ row0Sigma s w = 0 := by
  have hEq := row0Sigma_eq_convCoeff_rev (s := s) (w := w)
  constructor
  · intro h
    calc
      row0Sigma s w = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 := hEq
      _ = 0 := h
  · intro h
    calc
      convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = row0Sigma s w := by
        exact Eq.symm hEq
      _ = 0 := h

/-- Generic reduction at n=4 to the closed form linear combination. -/
theorem tail4_iff_lincomb
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0
      ↔ (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 := by
  have hEq := convCoeff4_eq_lincomb (s := s) (w := w)
  constructor
  · intro h
    -- rewrite (JetQuotOp.σ2 s * w 0 + (-2)*w 1) into convCoeff ... 4
    calc
      (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1)
          = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 := by
              exact Eq.symm hEq
      _ = 0 := h
  · intro h
    calc
      convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4
          = (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) := hEq
      _ = 0 := h

/-- Generic reduction at n=5 to `w 0 = 0` (since `(-2:ℂ) ≠ 0`). -/
theorem tail5_iff_w0
    (s : OffSeed Xi) (w : Transport.Window 3) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 ↔ (w 0) = 0 := by
  have hEq := convCoeff5_eq_lincomb (s := s) (w := w)
  constructor
  · intro hn
    -- Convert hn into (-2)*w0 = 0 by rewriting, no simp.
    have hmul : (-2 : ℂ) * (w 0) = 0 := by
      calc
        (-2 : ℂ) * (w 0)
            = convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 := by
                exact Eq.symm hEq
        _ = 0 := hn
    -- Cancel (-2) ≠ 0.
    have hmul' := mul_eq_zero.mp hmul
    cases hmul' with
    | inl h2 =>
        have : (-2 : ℂ) ≠ 0 := by norm_num
        exact False.elim (this h2)
    | inr hw0 =>
        exact hw0
  · intro hw0
    -- Convert back using hEq.
    have : (-2 : ℂ) * (w 0) = 0 := by simpa [hw0]
    calc
      convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5
          = (-2 : ℂ) * (w 0) := hEq
      _ = 0 := this

/-!
### Specialised versions for the three canonical windows
-/

theorem tail3_w0At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
      ↔ row0Sigma s (w0At m s) = 0 :=
  tail3_iff_row0Sigma (s := s) (w := w0At m s)

theorem tail3_wp2At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
      ↔ row0Sigma s (wp2At m s) = 0 :=
  tail3_iff_row0Sigma (s := s) (w := wp2At m s)

theorem tail3_wp3At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0
      ↔ row0Sigma s (wp3At m s) = 0 :=
  tail3_iff_row0Sigma (s := s) (w := wp3At m s)

theorem tail4_w0At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0
      ↔ (JetQuotOp.σ2 s) * ((w0At m s) 0) + (-2 : ℂ) * ((w0At m s) 1) = 0 :=
  tail4_iff_lincomb (s := s) (w := w0At m s)

theorem tail4_wp2At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0
      ↔ (JetQuotOp.σ2 s) * ((wp2At m s) 0) + (-2 : ℂ) * ((wp2At m s) 1) = 0 :=
  tail4_iff_lincomb (s := s) (w := wp2At m s)

theorem tail4_wp3At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0
      ↔ (JetQuotOp.σ2 s) * ((wp3At m s) 0) + (-2 : ℂ) * ((wp3At m s) 1) = 0 :=
  tail4_iff_lincomb (s := s) (w := wp3At m s)

theorem tail5_w0At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0
      ↔ ((w0At m s) 0) = 0 :=
  tail5_iff_w0 (s := s) (w := w0At m s)

theorem tail5_wp2At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0
      ↔ ((wp2At m s) 0) = 0 :=
  tail5_iff_w0 (s := s) (w := wp2At m s)

theorem tail5_wp3At_iff (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0
      ↔ ((wp3At m s) 0) = 0 :=
  tail5_iff_w0 (s := s) (w := wp3At m s)

end Tail345Reductions

end XiPacket
end Targets
end Hyperlocal
