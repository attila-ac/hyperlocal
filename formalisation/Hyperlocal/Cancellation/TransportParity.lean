/-
  Hyperlocal/Cancellation/TransportParity.lean

  Minimal bridge: import the Toeplitz/transport interface and expose
  the parity-equivariance lemma inside the Cancellation layer.
-/

import Hyperlocal.Transport.ToeplitzInterface

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open Hyperlocal.Transport

-- Re-export (or restate) the key lemma you want to cite from Cancellation:
-- Adjust the lemma name below to the exact one you proved in ToeplitzInterface.lean.
theorem transported_TAC_has_parity {n : ℕ} (x : Window (n + 1)) :
    parity (shiftR x) = shiftL (parity x) := by
  simpa using (parity_shiftR_eq_shiftL_parity (n := n) x)

end PrimeWitness
end Cancellation
end Hyperlocal
