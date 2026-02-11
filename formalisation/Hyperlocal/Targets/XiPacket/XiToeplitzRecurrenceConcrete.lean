/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceConcrete.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Concrete recurrence row functional for a given prime `p` (to be implemented). -/
axiom XiRecRow (s : Hyperlocal.OffSeed Xi) (p : ℝ) :
  (Fin 3 → ℝ) →ₗ[ℝ] ℝ

/-- Nontriviality for the two primes we use. -/
axiom XiRecRow_ne_zero_2 (s : Hyperlocal.OffSeed Xi) : XiRecRow s (2 : ℝ) ≠ 0
axiom XiRecRow_ne_zero_3 (s : Hyperlocal.OffSeed Xi) : XiRecRow s (3 : ℝ) ≠ 0

/-- Window annihilations for p=2. -/
axiom XiRecRow_w0_2 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (2 : ℝ) (reVec3 (w0 s)) = 0
axiom XiRecRow_wc_2 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (2 : ℝ) (reVec3 (wc s)) = 0
axiom XiRecRow_wp2 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (2 : ℝ) (reVec3 (wp2 s)) = 0

/-- Window annihilations for p=3. -/
axiom XiRecRow_w0_3 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (3 : ℝ) (reVec3 (w0 s)) = 0
axiom XiRecRow_wc_3 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (3 : ℝ) (reVec3 (wc s)) = 0
axiom XiRecRow_wp3 (s : Hyperlocal.OffSeed Xi) :
  XiRecRow s (3 : ℝ) (reVec3 (wp3 s)) = 0

end Hyperlocal.Targets.XiPacket
