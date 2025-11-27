/-
  Hyperlocal/Cancellation/InstabilityK1.lean

  k = 1 instability:
  • keeps current placeholder instance (nothing breaks today);
  • adds TWO “upgrade hooks” for the real proof:
      (1) a *record-free* cover combinator,
      (2) a collision-proof record `K1RegionCover`.

  Use whichever when you wire in the asymptotics + mid-range UC check.
-/

import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1

/-- TODAY: placeholder (keeps everything working).
    Replace with the genuine characteristic–root argument later. -/
theorem unstable_k1_all_t (A t : ℝ) : UnstableHom 1 A t :=
  ⟨trivial⟩

/-- Instance for typeclass search / `haveI`. -/
instance instUnstable_k1 (A t : ℝ) : UnstableHom 1 A t :=
  unstable_k1_all_t A t

/-- UPGRADE HOOK (record-free): cover `(0,∞)` by three regions and
    get global instability. Use this if want to avoid any
    structure/namespace ambiguity. -/
theorem unstable_k1_all_t_of_small_mid_large
    (A t1 t2 : ℝ)
    (h0  : 0 < t1) (h12 : t1 ≤ t2)
    (small : ∀ {t : ℝ}, 0 < t → t ≤ t1 → UnstableHom 1 A t)
    (mid   : ∀ {t : ℝ}, t1 ≤ t → t ≤ t2 → UnstableHom 1 A t)
    (large : ∀ {t : ℝ}, t2 ≤ t → UnstableHom 1 A t) :
    ∀ {t : ℝ}, 0 < t → UnstableHom 1 A t := by
  intro t ht
  rcases lt_or_ge t t1 with hlt | hge1
  · exact small (by exact ht) (le_of_lt hlt)
  · rcases le_total t t2 with hle2 | hge2
    · exact mid (by exact hge1) (by exact hle2)
    · exact large (by exact hge2)

/-- 🔌 UPGRADE HOOK (recorded data): if prefer a single object to
    package the cover, use this *distinctly named* record to avoid
    clashing with anything called `RegionCover` elsewhere. -/
structure K1RegionCover (A : ℝ) : Type where
  t1 : ℝ
  t2 : ℝ
  h0  : 0 < t1
  h12 : t1 ≤ t2
  small : ∀ {t : ℝ}, 0 < t → t ≤ t1 → UnstableHom 1 A t
  mid   : ∀ {t : ℝ}, t1 ≤ t → t ≤ t2 → UnstableHom 1 A t
  large : ∀ {t : ℝ}, t2 ≤ t → UnstableHom 1 A t

/-- Global instability from a packaged cover (record version). -/
theorem unstable_k1_all_t_of_cover
    (A : ℝ) (cov : K1RegionCover A) :
    ∀ {t : ℝ}, 0 < t → UnstableHom 1 A t := by
  intro t ht
  rcases lt_or_ge t cov.t1 with hlt | hge1
  · exact cov.small (by exact ht) (le_of_lt hlt)
  · rcases le_total t cov.t2 with hle2 | hge2
    · exact cov.mid (by exact hge1) (by exact hle2)
    · exact cov.large (by exact hge2)

/-- Handy export if want a typeclass instance from a cover. -/
theorem inst_from_cover
    (A t : ℝ) (cov : K1RegionCover A) (ht : 0 < t) :
    UnstableHom 1 A t :=
  unstable_k1_all_t_of_cover A cov ht

/-- **Smoke test**: once the k=1 instance is available, any bridge
    and the Combine “only zero is fine-tuned” fact yield a contradiction. -/
theorem k1_contradiction
    (A t : ℝ)
    (bridge : BridgeData 1 A t)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0) : False := by
  haveI : UnstableHom 1 A t := instUnstable_k1 A t
  exact no_cancellation_if_unstable bridge combine_only_zero

end InstabilityK1
end Cancellation
end Hyperlocal
