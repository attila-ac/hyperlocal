import Hyperlocal.Transport.OffSeedStripBridge
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.RiemannZeta
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport
open Complex

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem offSeed_in_critical_strip_of_trueanalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    0 < s.ρ.re ∧ s.ρ.re < 1 := by
  have hρ0 : s.ρ ≠ 0 := by
    intro h0
    apply s.ht
    simpa [h0]

  have hρ1 : s.ρ ≠ 1 := by
    intro h1
    apply s.ht
    simpa [h1]

  have h1mρ0 : 1 - s.ρ ≠ 0 := by
    intro h
    apply hρ1
    simpa [eq_comm] using (sub_eq_zero.mp h)

  have hΛ0 :
      completedRiemannZeta₀ s.ρ =
        completedRiemannZeta s.ρ + 1 / s.ρ + 1 / (1 - s.ρ) := by
    have hEq :
        completedRiemannZeta s.ρ =
          completedRiemannZeta₀ s.ρ - 1 / s.ρ - 1 / (1 - s.ρ) :=
      completedRiemannZeta_eq (s := s.ρ)
    have hEq' :=
      congrArg (fun z : ℂ => z + (1 / s.ρ + 1 / (1 - s.ρ))) hEq
    have :
        completedRiemannZeta s.ρ + (1 / s.ρ + 1 / (1 - s.ρ)) =
          completedRiemannZeta₀ s.ρ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
    simpa [add_assoc, add_left_comm, add_comm] using this.symm

  have hxi_factor :
      Hyperlocal.xi s.ρ =
        s.ρ * (s.ρ - 1) * completedRiemannZeta s.ρ := by
    calc
      Hyperlocal.xi s.ρ
          = s.ρ * (s.ρ - 1) *
              (completedRiemannZeta s.ρ + 1 / s.ρ + 1 / (1 - s.ρ)) + 1 := by
              simp [Hyperlocal.xi, hΛ0]
      _ = s.ρ * (s.ρ - 1) * completedRiemannZeta s.ρ := by
            field_simp [hρ0, h1mρ0]
            ring

  have hxi0 : Hyperlocal.xi s.ρ = 0 := by
    simpa using s.hρ

  have hCompleted : completedRiemannZeta s.ρ = 0 := by
    have hmul : s.ρ * (s.ρ - 1) * completedRiemannZeta s.ρ = 0 := by
      simpa [hxi_factor] using hxi0
    have hmul' : s.ρ * ((s.ρ - 1) * completedRiemannZeta s.ρ) = 0 := by
      simpa [mul_assoc] using hmul
    rcases mul_eq_zero.mp hmul' with hzero | hrest
    · exact False.elim (hρ0 hzero)
    · rcases mul_eq_zero.mp hrest with hsub | hcomp
      · exact False.elim (hρ1 (sub_eq_zero.mp hsub))
      · exact hcomp

  have hZeta : Hyperlocal.zeta s.ρ = 0 := by
    simpa [Hyperlocal.zeta, riemannZeta_def_of_ne_zero hρ0, hCompleted]

  have hRe_lt_one : s.ρ.re < 1 := by
    by_contra hnot
    have hge : 1 ≤ s.ρ.re := le_of_not_gt hnot
    exact (riemannZeta_ne_zero_of_one_le_re (s := s.ρ) hge) (by
      simpa [Hyperlocal.zeta] using hZeta)

  have hCompleted_one_sub : completedRiemannZeta (1 - s.ρ) = 0 := by
    simpa [completedRiemannZeta_one_sub] using hCompleted

  have hZeta_one_sub : Hyperlocal.zeta (1 - s.ρ) = 0 := by
    simpa [Hyperlocal.zeta, riemannZeta_def_of_ne_zero h1mρ0, hCompleted_one_sub]

  have hRe_pos : 0 < s.ρ.re := by
    by_contra hnot
    have hle : s.ρ.re ≤ 0 := le_of_not_gt hnot
    have hge : 1 ≤ (1 - s.ρ).re := by
      have : 1 ≤ 1 - s.ρ.re := by
        linarith
      simpa using this
    exact (riemannZeta_ne_zero_of_one_le_re (s := 1 - s.ρ) hge) (by
      simpa [Hyperlocal.zeta] using hZeta_one_sub)

  exact ⟨hRe_pos, hRe_lt_one⟩

noncomputable def offSeedStrip_of_trueanalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    _root_.Hyperlocal.OffSeedStrip Xi := by
  rcases offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  exact mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)

end XiPacket
end Targets
end Hyperlocal
