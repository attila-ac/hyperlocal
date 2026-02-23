/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_RangeReindex.lean

  Step 3 continuation (finitary):

  Reindex the filter-sum form (upper-triangular) into a canonical truncation sum
  over `Finset.range (N - j)`.

  Snapshot-robust trick:
  use `(Finset.range ...).attach` so membership proofs live in the index, not in lambdas.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_Finite
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open scoped BigOperators

/--
Reindex a filtered sum over `Fin N` (those `m` with `j ≤ m`) into an attached-range sum
over `r ∈ range (N - j)`.
-/
theorem sum_filter_ge_reindex_range_attach
    (N : ℕ) (j : Fin N) (F : Fin N → ℂ) :
    ((Finset.univ.filter (fun m : Fin N => j ≤ m)).sum F)
      =
    ((Finset.range (N - (j : ℕ))).attach).sum (fun r =>
      F ⟨(j : ℕ) + r.1,
        by
          have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
          have hr : r.1 < N - (j : ℕ) := Finset.mem_range.mp r.2
          have h := Nat.add_lt_add_left hr (j : ℕ)
          simpa [Nat.sub_add_cancel hj] using h⟩) := by
  classical

  let s : Finset (Fin N) := Finset.univ.filter (fun m : Fin N => j ≤ m)
  let t : Finset { r // r ∈ Finset.range (N - (j : ℕ)) } :=
    (Finset.range (N - (j : ℕ))).attach

  -- The reindex map: m ↦ (m - j)
  let i : ∀ m : Fin N, m ∈ s → { r // r ∈ Finset.range (N - (j : ℕ)) } :=
    fun m hm =>
      ⟨(m : ℕ) - (j : ℕ),
        by
          have hmj : (j : ℕ) ≤ (m : ℕ) := (Finset.mem_filter.mp hm).2
          have hjN : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
          -- prove (m-j) < (N-j) by adding j and rewriting to m < N
          have hlt_add :
              ((m : ℕ) - (j : ℕ)) + (j : ℕ) < (N - (j : ℕ)) + (j : ℕ) := by
            -- LHS = m, RHS = N
            simpa [Nat.sub_add_cancel hmj, Nat.sub_add_cancel hjN] using m.isLt
          have hlt : (m : ℕ) - (j : ℕ) < N - (j : ℕ) :=
            Nat.lt_of_add_lt_add_right hlt_add
          exact Finset.mem_range.mpr hlt⟩

  -- The inverse map: r ↦ (j + r)
  let inv : { r // r ∈ Finset.range (N - (j : ℕ)) } → Fin N :=
    fun r =>
      ⟨(j : ℕ) + r.1,
        by
          have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
          have hr : r.1 < N - (j : ℕ) := Finset.mem_range.mp r.2
          have h := Nat.add_lt_add_left hr (j : ℕ)
          simpa [Nat.sub_add_cancel hj] using h⟩

  -- Use `sum_bij` (NOTE: obligation order in this snapshot is:
  --   mem → inj → surj → compatibility)
  refine Finset.sum_bij
    (s := s) (t := t)
    (i := i)
    (f := fun m => F m)
    (g := fun r => F (inv r))
    ?_ ?_ ?_ ?_
  · -- mem: image lands in `t`
    intro m hm
    simp [t, i]
  · -- inj: if i m₁ hm₁ = i m₂ hm₂ then m₁ = m₂
    intro m₁ hm₁ m₂ hm₂ hEq
    have hval : ((m₁ : ℕ) - (j : ℕ)) = ((m₂ : ℕ) - (j : ℕ)) :=
      congrArg Subtype.val hEq
    have hmj₁ : (j : ℕ) ≤ (m₁ : ℕ) := (Finset.mem_filter.mp hm₁).2
    have hmj₂ : (j : ℕ) ≤ (m₂ : ℕ) := (Finset.mem_filter.mp hm₂).2
    apply Fin.ext
    -- m = (m-j)+j (since j ≤ m)
    calc
      (m₁ : ℕ) = ((m₁ : ℕ) - (j : ℕ)) + (j : ℕ) := (Nat.sub_add_cancel hmj₁).symm
      _ = ((m₂ : ℕ) - (j : ℕ)) + (j : ℕ) := by simpa [hval]
      _ = (m₂ : ℕ) := Nat.sub_add_cancel hmj₂
  · -- surj: every r ∈ t comes from m = inv r
    intro r hr
    refine ⟨inv r, ?_, ?_⟩
    · -- inv r ∈ s (i.e. j ≤ j+r)
      have hjmNat : (j : ℕ) ≤ (j : ℕ) + r.1 := Nat.le_add_right _ _
      -- convert Nat ≤ to Fin ≤
      have : j ≤ (inv r) := hjmNat
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    · -- i (inv r) _ = r
      apply Subtype.ext
      -- (j + r) - j = r
      simpa [inv, Nat.add_sub_cancel_left, i]
  · -- compatibility: summands match
    intro m hm
    -- show inv (i m hm) = m, then simp
    have hmj : (j : ℕ) ≤ (m : ℕ) := (Finset.mem_filter.mp hm).2
    have hadd : (j : ℕ) + ((m : ℕ) - (j : ℕ)) = (m : ℕ) :=
      Nat.add_sub_of_le hmj
    have hinv : inv (i m hm) = m := by
      apply Fin.ext
      -- unfold and use hadd
      simp [inv, i, hadd]
    simpa [hinv]

/--
Step-3 endpoint for `transport`:

Convert the snapshot-robust filter-sum formula into a canonical truncation sum indexed by
`(Finset.range (N - j)).attach`.
-/
theorem transport_apply_eq_truncSum_finite_attach
    (N : ℕ) (Γ : Fin N → ℂ) (δ : ℂ) (j : Fin N) :
    transport N δ Γ j
      =
    ((Finset.range (N - (j : ℕ))).attach).sum (fun r =>
      ((δ ^ r.1) / (Nat.factorial r.1 : ℂ))
        * Γ ⟨(j : ℕ) + r.1,
          by
            have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
            have hr : r.1 < N - (j : ℕ) := Finset.mem_range.mp r.2
            have h := Nat.add_lt_add_left hr (j : ℕ)
            simpa [Nat.sub_add_cancel hj] using h⟩) := by
  classical
  have h :=
    (transport_apply_eq_filterSum (N := N) (Γ := Γ) (δ := δ) (j := j))
  simpa using
    (h.trans
      (sum_filter_ge_reindex_range_attach (N := N) (j := j)
        (F := fun m =>
          ((δ ^ ((m : ℕ) - (j : ℕ))) / (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ))
            * Γ m)))

/--
Eliminate the `.attach` by reindexing to `Fin (N - j)`.

This is often the most stable “canonical truncation sum” form, since `r.isLt` supplies
the bound proof and lambdas stay clean.
-/
theorem transport_apply_eq_truncSum_finite_fin
    (N : ℕ) (Γ : Fin N → ℂ) (δ : ℂ) (j : Fin N) :
    transport N δ Γ j
      =
    (Finset.univ : Finset (Fin (N - (j : ℕ)))).sum (fun r =>
      ((δ ^ (r : ℕ)) / (Nat.factorial (r : ℕ) : ℂ))
        * Γ ⟨(j : ℕ) + (r : ℕ),
          by
            have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
            have hr : (r : ℕ) < N - (j : ℕ) := r.isLt
            have h := Nat.add_lt_add_left hr (j : ℕ)
            simpa [Nat.sub_add_cancel hj] using h⟩) := by
  classical

  -- Start from the attached truncation sum you already proved.
  rw [transport_apply_eq_truncSum_finite_attach (N := N) (Γ := Γ) (δ := δ) (j := j)]

  -- Reindex `(range ...).attach` to `Fin (N - j)` by `r ↦ ⟨r.1, mem_range.mp r.2⟩`.
  -- This is a clean bijection, so `Finset.sum_bij` is snapshot-robust here.
  let R : Finset { r // r ∈ Finset.range (N - (j : ℕ)) } :=
    (Finset.range (N - (j : ℕ))).attach

  let fR : { r // r ∈ Finset.range (N - (j : ℕ)) } → ℂ := fun r =>
    ((δ ^ r.1) / (Nat.factorial r.1 : ℂ))
      * Γ ⟨(j : ℕ) + r.1,
        by
          have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
          have hr : r.1 < N - (j : ℕ) := Finset.mem_range.mp r.2
          have h := Nat.add_lt_add_left hr (j : ℕ)
          simpa [Nat.sub_add_cancel hj] using h⟩

  -- Now show `R.sum fR = univ.sum (...)` by bijection `Subtype(range) ↔ Fin`.
  -- Map: ⟨r, r∈range⟩ ↦ ⟨r, mem_range.mp _⟩ : Fin (N-j)
  have hbij :
      R.sum fR
        =
      (Finset.univ : Finset (Fin (N - (j : ℕ)))).sum (fun r =>
        ((δ ^ (r : ℕ)) / (Nat.factorial (r : ℕ) : ℂ))
          * Γ ⟨(j : ℕ) + (r : ℕ),
            by
              have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
              have hr : (r : ℕ) < N - (j : ℕ) := r.isLt
              have h := Nat.add_lt_add_left hr (j : ℕ)
              simpa [Nat.sub_add_cancel hj] using h⟩) := by
    -- `Finset.sum_bij` between `R` and `univ : Finset (Fin (N-j))`.
    refine Finset.sum_bij
      (s := R)
      (t := (Finset.univ : Finset (Fin (N - (j : ℕ)))))
      (i := fun r _ => (⟨r.1, Finset.mem_range.mp r.2⟩ : Fin (N - (j : ℕ))))
      (f := fR)
      (g := fun r =>
        ((δ ^ (r : ℕ)) / (Nat.factorial (r : ℕ) : ℂ))
          * Γ ⟨(j : ℕ) + (r : ℕ),
            by
              have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
              have hr : (r : ℕ) < N - (j : ℕ) := r.isLt
              have h := Nat.add_lt_add_left hr (j : ℕ)
              simpa [Nat.sub_add_cancel hj] using h⟩)
      ?_ ?_ ?_ ?_
    · intro r hr
      simp
    · intro r₁ hr₁ r₂ hr₂ h
      apply Subtype.ext
      -- equality in `Fin` gives equality of values
      exact congrArg Fin.val h
    · intro r hr
      -- surjectivity: given `r : Fin (N-j)`, preimage is `⟨r, mem_range.mpr r.isLt⟩`
      refine ⟨⟨(r : ℕ), Finset.mem_range.mpr r.isLt⟩, ?_, ?_⟩
      · -- membership in `R`
        simp [R]
      · -- mapping back gives `r`
        -- in `Fin`, ext on values
        apply Fin.ext
        rfl
    · intro r hr
      -- compatibility of summands: definitional after unfolding
      -- `r.1` is the Nat value used on both sides
      simp [fR]

  -- Finish
  simpa [R, fR] using hbij

  -- NOTE: this `simpa` is purely definitional clean-up; lint may warn but it's harmless.

end TAC
end XiPacket
end Targets
end Hyperlocal
