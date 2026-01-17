/-
# Hyperlocal: Smoke checks (top level)

A tiny file that #checks the named statements the manuscript relies on.
This compiles quickly and is great for demos or CI “green light” checks.
-/

-- Core + minimal model
import Hyperlocal.Core
import Hyperlocal.MinimalModel

-- Factorisation + symmetry inheritance for G
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC

-- Recurrence layer
import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Cancellation.RecurrenceWithFinsetSum

-- Cancellation stack + umbrella theorem
import Hyperlocal.All

noncomputable section

-- === MinimalModel: local data at the quartet polynomial ===
#check Hyperlocal.MinimalModel.quartet_derivative_at_seed
#check Hyperlocal.MinimalModel.quartetPow_derivative_at_seed_is_zero

-- === Factorization: FE/RC inheritance for G off the zero set of R ===
#check Hyperlocal.Factorization.G_inherits_FE_off_zeros
#check Hyperlocal.FactorizationRC.G_inherits_RC_off_zeros

-- === Recurrence: Cauchy-product pivot identity & API ===
#check Hyperlocal.Cancellation.recurrence_coeff_k
#check Hyperlocal.Cancellation.RecSpec   -- the recurrence record/API

-- === Cancellation bridge: abstract wrap to contradiction ===
#check Hyperlocal.Cancellation.no_cancellation_if_unstable
