-- Hyperlocal/Cancellation/InstabilityK1_Fillers.lean
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.InstabilityK1  -- for the hooks added

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1

/-- Small-t hypothesis container. -/
structure SmallHyp (A t1 : ℝ) : Prop :=
  (h0   : 0 < t1)
  (prove : ∀ {t : ℝ}, 0 < t → t ≤ t1 → UnstableHom 1 A t)

/-- Mid-range hypothesis container. -/
structure MidHyp (A t1 t2 : ℝ) : Prop :=
  (h12  : t1 ≤ t2)
  (prove : ∀ {t : ℝ}, t1 ≤ t → t ≤ t2 → UnstableHom 1 A t)

/-- Large-t hypothesis container. -/
structure LargeHyp (A t2 : ℝ) : Prop :=
  (prove : ∀ {t : ℝ}, t2 ≤ t → UnstableHom 1 A t)

/-- Glue the 3 regions into a global statement over `(0, ∞)`. -/
theorem unstable_from_fillers
  {A t1 t2 : ℝ}
  (S : SmallHyp A t1) (M : MidHyp A t1 t2) (L : LargeHyp A t2) :
  ∀ {t : ℝ}, 0 < t → UnstableHom 1 A t := by
  intro t ht
  rcases lt_or_ge t t1 with hlt | hge1
  · exact S.prove (by exact ht) (le_of_lt hlt)
  · rcases le_total t t2 with hle2 | hge2
    · exact M.prove (by exact hge1) (by exact hle2)
    · exact L.prove (by exact hge2)

end InstabilityK1
end Cancellation
end Hyperlocal
