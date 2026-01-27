/-
# Hyperlocal (Manuscript order umbrella)

This is a *thin* umbrella that imports the project in the same order
the manuscript presents the argument. It doesn’t add new facts — it’s
just here so readers/referees can `lake build Hyperlocal.Manuscript.All`
and know they’re seeing the whole pipeline in paper order.

Sections:
1) Ad absurdum setup & quartet propagation (Core).
2) Minimal model + local derivatives (MinimalModel).
3) Factorisation interface + FE inheritance for G (Factorization).
4) RC inheritance for G (FactorizationRC).
5) Algebraic recurrence layer (Recurrence*).
6) Jet/QCC/TRC/Combine (Cancellation::*).
7) Instability hook + k=1,k=2 instances (Instability*).
-/

import Hyperlocal.Core

-- Minimal polynomial model (quartet) and derivative facts
import Hyperlocal.MinimalModel

-- Factorisation layer: H = R_{ρ,k} * G and FE inheritance for G (off the zero set)
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC

-- Algebraic recurrences (Cauchy-product pivot + Finset API)
import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Cancellation.RecurrenceWithFinsetSum

-- Jets, QCC/TRC and their intersection at (A₀, t₀)
import Hyperlocal.Cancellation.Solo
import Hyperlocal.Cancellation.Setup
import Hyperlocal.Cancellation.QCC
import Hyperlocal.Cancellation.TRC
import Hyperlocal.Cancellation.Combine
import Hyperlocal.Cancellation.Rank
import Hyperlocal.Cancellation.Solo12

-- Instability hook + concrete k=1,2 stubs/instances (as available)
import Hyperlocal.Cancellation.InstabilityHyp

-- Prime witness endpoint / parity bridge / TAC endpoint
import Hyperlocal.Cancellation.PrimeWitness
import Hyperlocal.Cancellation.PrimeWitnessParity
import Hyperlocal.Transport.TAC
import Hyperlocal.Transport.Exports

noncomputable section

/- This module is intentionally empty: it just imports everything in the
   manuscript’s narrative order so the project can be built end-to-end. -/
namespace Hyperlocal
namespace Manuscript

end Manuscript
end Hyperlocal
