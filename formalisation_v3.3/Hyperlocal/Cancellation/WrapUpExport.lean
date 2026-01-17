import Hyperlocal.Cancellation.WrapUp
/-!
  Hyperlocal/Cancellation/WrapUpExport.lean

  Tiny helper that re-exports the final wrappers into
  `Hyperlocal.Cancellation` so users can write
    `Hyperlocal.Cancellation.no_off_critical_zero_k1`
  instead of going through the `WrapUp` sub-namespace.
-/

noncomputable section
namespace Hyperlocal
namespace Cancellation

export WrapUp (no_off_critical_zero_k1 no_off_critical_zero_k2)

end Cancellation
end Hyperlocal
