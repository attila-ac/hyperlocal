/-
  Hyperlocal/Targets/XiTransportStencil2.lean

  Step 3: explicit closed-form stencil for `XiTransportOp 2`.

  Goal:
    Expose the three coordinates of (XiTransportOp 2 s) w in terms of δ := delta s
    and the window entries w0,w1,w2.

  Design:
    * Use the already-green `toeplitzR₂_apply0/1/2` lemmas from XiTransportConvolution.
    * Specialize to `coeffs := shiftCoeff (delta s)`.
    * Prove tiny simp lemmas for `shiftCoeff δ` at 0/1/2 only.
-/

import Hyperlocal.Targets.XiTransportConvolution
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiTransport

open scoped BigOperators
open Complex
open Hyperlocal.Transport   -- IMPORTANT: brings `Window`, `toeplitzR`, etc into scope

/-
  Tiny simp lemmas for the stencil coefficients `shiftCoeff`.
-/

@[simp] lemma shiftCoeff_zero (δ : ℝ) :
    shiftCoeff δ 0 = (1 : ℂ) := by
  simp [shiftCoeff]

@[simp] lemma shiftCoeff_one (δ : ℝ) :
    shiftCoeff δ 1 = (δ : ℂ) := by
  simp [shiftCoeff]

@[simp] lemma shiftCoeff_two (δ : ℝ) :
    shiftCoeff δ 2 = ((δ : ℂ) ^ 2) / (2 : ℂ) := by
  simp [shiftCoeff]

/-
  Core stencil formulas (n=2), written in a way that matches your existing simp-lemmas.
-/

theorem XiTransportOp₂_coord0 (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 0
      =
    (shiftCoeff (delta s) 0) * (w 0) := by
  -- XiTransportOp 2 s = toeplitzR 2 (shiftCoeff (delta s))
  simp [XiTransportOp]

theorem XiTransportOp₂_coord1 (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 1
      =
    (shiftCoeff (delta s) 0) * (w 1) + (shiftCoeff (delta s) 1) * (w 0) := by
  simp [XiTransportOp]

theorem XiTransportOp₂_coord2 (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 2
      =
    (shiftCoeff (delta s) 0) * (w 2)
      + (shiftCoeff (delta s) 1) * (w 1)
      + (shiftCoeff (delta s) 2) * (w 0) := by
  simp [XiTransportOp]

/-
  “Explicit δ^k/k!” versions (the ones you actually want for matching to Toeplitz/transport entries).
-/

theorem XiTransportOp₂_coord0_explicit (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 0 = w 0 := by
  simpa [XiTransportOp₂_coord0]

theorem XiTransportOp₂_coord1_explicit (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 1 = w 1 + (delta s : ℂ) * w 0 := by
  -- expand coord1 then simp shiftCoeff at 0/1
  simpa [XiTransportOp₂_coord1, add_assoc, add_comm, add_left_comm, mul_assoc]

theorem XiTransportOp₂_coord2_explicit (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (XiTransportOp 2 s) w 2
      =
    w 2 + (delta s : ℂ) * w 1 + ((delta s : ℂ) ^ 2) / (2 : ℂ) * w 0 := by
  -- expand coord2 then simp shiftCoeff at 0/1/2
  simpa [XiTransportOp₂_coord2, add_assoc, add_comm, add_left_comm, mul_assoc]

end XiTransport
end Targets
end Hyperlocal
