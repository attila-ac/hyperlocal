/-
  Hyperlocal/Targets/XiPacket/XiWindowPayloadConstructor.lean

  Phase 4 (Plan C++):
  PURE construction (Type-valued): no ξ-semantic proofs.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Generic Phase-4 constructor: build `WindowPayload σ t` from B/C facts about five windows. -/
def windowPayload_mk_of_BC
    {σ t : ℝ}
    (W0 Wc Ws Wp2 Wp3 : Transport.Window 3)

    -- Lemma B (Trig split) at p=2,3
    (hW2 :
      ∀ i : Fin 3,
        Wp2 i = W0 i
          + ((aCoeff σ t (2 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff σ t (2 : ℝ) : ℂ) * (Ws i)))
    (hW3 :
      ∀ i : Fin 3,
        Wp3 i = W0 i
          + ((aCoeff σ t (3 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff σ t (3 : ℝ) : ℂ) * (Ws i)))

    -- Lemma C (ell/kappa consequences)
    (hEll2 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp2) = 0)
    (hEll3 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp3) = 0)
    (hKap  : Transport.kappa (reVec3 W0) (reVec3 Wc) (reVec3 Ws) ≠ 0)
    :
    WindowPayload σ t := by
  refine
    { w0 := W0
      wc := Wc
      ws := Ws
      wp2 := Wp2
      wp3 := Wp3
      hw2 := hW2
      hw3 := hW3
      hell2 := hEll2
      hell3 := hEll3
      hkappa := hKap }

/--
Same constructor packaged for off-seeds:
build `WindowPayload s.ρ.re s.ρ.im` once you instantiate windows + B/C facts.
-/
def windowPayload_mk_of_BC_offSeed
    {H : ℂ → ℂ} (s : Hyperlocal.OffSeed H)
    (W0 Wc Ws Wp2 Wp3 : Transport.Window 3)

    -- Lemma B (Trig split) at p=2,3 using σ=s.ρ.re and t=s.ρ.im
    (hW2 :
      ∀ i : Fin 3,
        Wp2 i = W0 i
          + ((aCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * (Ws i)))
    (hW3 :
      ∀ i : Fin 3,
        Wp3 i = W0 i
          + ((aCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * (Ws i)))

    -- Lemma C (ell/kappa consequences)
    (hEll2 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp2) = 0)
    (hEll3 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp3) = 0)
    (hKap  : Transport.kappa (reVec3 W0) (reVec3 Wc) (reVec3 Ws) ≠ 0)
    :
    WindowPayload s.ρ.re s.ρ.im := by
  -- `windowPayload_mk_of_BC` is a `def`, so we just apply it as a term.
  simpa using
    (windowPayload_mk_of_BC (σ := s.ρ.re) (t := s.ρ.im)
      W0 Wc Ws Wp2 Wp3 hW2 hW3 hEll2 hEll3 hKap)

end XiPacket
end Targets
end Hyperlocal
