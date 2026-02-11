/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceMinimalModelProof.lean

  Manufacturing layer:
  from a concrete jet-quotient row functional `XiRecRow s p`
  produce the stencil `c : Fin 3 → ℝ` and hence `XiMinimalModelRecurrenceHyp s`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceConcrete
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- Standard basis function `e i : Fin 3 → ℝ` (1 at i, 0 elsewhere). -/
private def e (i : Fin 3) : Fin 3 → ℝ := fun j => if j = i then (1 : ℝ) else 0

/-- Coordinates of a linear functional in the standard basis `e i`. -/
def rowVec (L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) : Fin 3 → ℝ :=
  fun i => L (e i)

/-- Decompose any `v : Fin 3 → ℝ` in the standard basis (explicit). -/
private lemma v_eq_lincomb_e (v : Fin 3 → ℝ) :
    v =
      (v (0 : Fin 3)) • e (0 : Fin 3)
    + (v (1 : Fin 3)) • e (1 : Fin 3)
    + (v (2 : Fin 3)) • e (2 : Fin 3) := by
  funext j
  fin_cases j <;> simp [e]

/--
Explicit (Fin 3) expansion:
`L v = ∑ i, (rowVec L i) * v i`.
-/
lemma rowVec_sum_eq (L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (v : Fin 3 → ℝ) :
    (∑ i : Fin 3, rowVec L i * v i) = L v := by
  classical
  let v0 : ℝ := v (0 : Fin 3)
  let v1 : ℝ := v (1 : Fin 3)
  let v2 : ℝ := v (2 : Fin 3)

  have hv : v = v0 • e (0 : Fin 3) + v1 • e (1 : Fin 3) + v2 • e (2 : Fin 3) := by
    simpa [v0, v1, v2] using (v_eq_lincomb_e (v := v))

  have hsum :
      (∑ i : Fin 3, rowVec L i * v i)
        =
        rowVec L (0 : Fin 3) * v0
      + rowVec L (1 : Fin 3) * v1
      + rowVec L (2 : Fin 3) * v2 := by
    -- just expand the finite sum; replace `v (k)` by `vk`
    simp [Fin.sum_univ_three, v0, v1, v2]

  -- compute `L v` by rewriting `v` into the basis, then using linearity
  have hLv :
      L v
        =
        (v0 * rowVec L (0 : Fin 3))
      + (v1 * rowVec L (1 : Fin 3))
      + (v2 * rowVec L (2 : Fin 3)) := by
    -- rewrite v
    rw [hv]
    -- split the two additions
    rw [map_add]
    rw [map_add]
    -- push scalars through L
    rw [map_smul]
    rw [map_smul]
    rw [map_smul]
    -- turn `•` on ℝ into `*`, and `rowVec` into `L (e i)`
    simp [rowVec, v0, v1, v2, smul_eq_mul]

  -- finish by rewriting both sides to explicit 3-term forms and commuting multiplications
  rw [hsum]
  -- goal is now: (rowVec*vk) sum = L v; rewrite `L v` using hLv, then normalize
  rw [hLv]
  ring_nf

/-- `toeplitzRow3 (rowVec L) v` is exactly `L v = 0`. -/
lemma toeplitzRow3_iff (L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (v : Fin 3 → ℝ) :
    toeplitzRow3 (rowVec L) v ↔ L v = 0 := by
  classical
  constructor
  · intro h
    -- rewrite the sum as `L v`
    simpa [toeplitzRow3, rowVec_sum_eq (L := L) (v := v)] using h
  · intro h
    simpa [toeplitzRow3, rowVec_sum_eq (L := L) (v := v)] using h

/-- If `L ≠ 0` then its coordinate row `rowVec L` is nonzero. -/
lemma rowVec_ne_zero_of_ne_zero (L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) :
    rowVec L ≠ 0 := by
  classical
  intro hrv
  apply hL
  -- prove `L = 0` by ext on the domain
  apply LinearMap.ext
  intro v
  have hs : (∑ i : Fin 3, rowVec L i * v i) = 0 := by
    simp [hrv]
  -- rewrite the sum as `L v`
  simpa [rowVec_sum_eq (L := L) (v := v)] using hs

/-- Main manufacturing lemma: the concrete recurrence rows imply the minimal-model hypothesis. -/
theorem xiMinimalModelRecurrenceHyp_fromConcrete (s : Hyperlocal.OffSeed Xi) :
    XiMinimalModelRecurrenceHyp s := by
  classical
  refine ⟨?h2, ?h3⟩

  · refine ⟨rowVec (XiRecRow s (2 : ℝ)),
      rowVec_ne_zero_of_ne_zero (L := XiRecRow s (2 : ℝ)) (XiRecRow_ne_zero_2 s),
      ?_, ?_, ?_⟩
    · exact (toeplitzRow3_iff (L := XiRecRow s (2 : ℝ)) (v := reVec3 (w0 s))).2 (XiRecRow_w0_2 s)
    · exact (toeplitzRow3_iff (L := XiRecRow s (2 : ℝ)) (v := reVec3 (wc s))).2 (XiRecRow_wc_2 s)
    · exact (toeplitzRow3_iff (L := XiRecRow s (2 : ℝ)) (v := reVec3 (wp2 s))).2 (XiRecRow_wp2 s)

  · refine ⟨rowVec (XiRecRow s (3 : ℝ)),
      rowVec_ne_zero_of_ne_zero (L := XiRecRow s (3 : ℝ)) (XiRecRow_ne_zero_3 s),
      ?_, ?_, ?_⟩
    · exact (toeplitzRow3_iff (L := XiRecRow s (3 : ℝ)) (v := reVec3 (w0 s))).2 (XiRecRow_w0_3 s)
    · exact (toeplitzRow3_iff (L := XiRecRow s (3 : ℝ)) (v := reVec3 (wc s))).2 (XiRecRow_wc_3 s)
    · exact (toeplitzRow3_iff (L := XiRecRow s (3 : ℝ)) (v := reVec3 (wp3 s))).2 (XiRecRow_wp3 s)

end XiPacket
end Targets
end Hyperlocal
