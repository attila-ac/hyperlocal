/-
  Hyperlocal/Targets/XiPacket/XiWindowBasisSimp.lean

  Minimal, robust simp facts for definitional Xi windows.

  Design:
  • DO NOT unfold `shiftR'` (avoids stuck `Fin.cases ... 1/2` goals).
  • Only use the computational simp lemmas `shiftR'_zero` / `shiftR'_succ`.
  • Keep proofs small and termination-safe (no simp-loops / maxRecDepth explosions).
-/

import Hyperlocal.Transport.ToeplitzLinearStep
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- For `j : Fin 2`, `j.castSucc : Fin 3` can never be `2`. -/
private lemma castSucc_ne_two (j : Fin 2) : (j.castSucc : Fin 3) ≠ (2 : Fin 3) := by
  intro h
  have hv : j.val = 2 := by
    -- `val (castSucc j) = val j`, and `val (2 : Fin 3) = 2`
    simpa using congrArg Fin.val h
  have : (2 : Nat) < 2 := by
    simpa [hv] using j.isLt
  exact (Nat.lt_irrefl 2 this)

/-- `shiftR'` kills the zero window (n=2 so windows have length 3). -/
@[simp] lemma shiftR'_zeroWindow : shiftR' (n := 2) (0 : Window 3) = 0 := by
  ext i
  refine Fin.cases ?h0 ?hs i
  · -- i = 0
    simp
  · -- i = succ j
    intro j
    simp

/-- `shiftR'` kills the last basis vector in window-3. -/
@[simp] lemma shiftR'_basisW3_two :
    shiftR' (n := 2) (basisW3 (2 : Fin 3)) = 0 := by
  ext i
  refine Fin.cases ?h0 ?hs i
  · -- i = 0
    simp [basisW3]
  · -- i = succ j, with j : Fin 2
    intro j
    -- shiftR' at succ uses `shiftR'_succ`, so we only have to evaluate `basisW3` at `j.castSucc`.
    simp [basisW3, castSucc_ne_two j]

/-- Double-shift of the last basis vector is also zero. -/
@[simp] lemma shiftR'_shiftR'_basisW3_two :
    shiftR' (n := 2) (shiftR' (n := 2) (basisW3 (2 : Fin 3))) = 0 := by
  -- apply `shiftR'` to `shiftR'_basisW3_two`
  simpa using congrArg (fun w => shiftR' (n := 2) w) shiftR'_basisW3_two

/-- Shifting the middle basis vector gives the last one. -/
@[simp] lemma shiftR'_basisW3_one :
    shiftR' (n := 2) (basisW3 (1 : Fin 3)) = basisW3 (2 : Fin 3) := by
  ext i
  refine Fin.cases ?h0 ?hs i
  · -- i = 0
    simp [basisW3]
  · -- i = j.succ
    intro j
    -- CRITICAL: kill `shiftR'` *before* turning `j` into concrete `0/1`,
    -- otherwise we get stuck with goals like `shiftR' _ 1 = ...`.
    simp [shiftR'_succ]
    -- now no `shiftR'` remains, so case-splitting `j` is safe
    fin_cases j <;> simp [basisW3]


/-- Double-shift of the middle basis vector is zero. -/
@[simp] lemma shiftR'_shiftR'_basisW3_one :
    shiftR' (n := 2) (shiftR' (n := 2) (basisW3 (1 : Fin 3))) = 0 := by
  -- apply `shiftR'` to `shiftR'_basisW3_one`, then use the `basisW3_two` lemma
  have h := congrArg (fun w => shiftR' (n := 2) w) shiftR'_basisW3_one
  -- h : shiftR'(shiftR'(basis 1)) = shiftR'(basis 2)
  simpa using h.trans shiftR'_basisW3_two

end XiPacket
end Targets
end Hyperlocal
