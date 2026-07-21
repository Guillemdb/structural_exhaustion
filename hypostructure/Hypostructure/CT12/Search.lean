import Hypostructure.CT12.State

/-!
# CT12 canonical peel and restoration selection

One generated `PeelStep` records the exact peeled value, exact finite options,
and canonical first restoration.  Its constructor is private, so no caller can
detach a choice from the predecessor state.
-/

namespace Hypostructure.CT12

universe uPrevious uState uPeeled uDemand uTier

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous}

/-- Framework-generated inspection of one positive-load state. -/
structure PeelStep (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier}
    Previous) (previous : Previous) {load : Nat}
    (state : spec.State previous (load + 1)) where
  private mk ::
  peeled : spec.Peeled state
  options : RestorationOptions (spec.State previous)
    (spec.DemandResidual previous) (spec.TierResidual previous) (load + 1)
  options_exact : options = spec.restorations peeled
  selected : Restoration (spec.State previous)
    (spec.DemandResidual previous) (spec.TierResidual previous) (load + 1)
  selected_exact : selected = options.selected
  selected_mem : List.Mem selected options.toList

/-- Compute the exact peel and let the framework select the first restoration. -/
def inspect (spec : Spec.{uPrevious, uState, uPeeled, uDemand, uTier} Previous)
    (previous : Previous) {load : Nat}
    (state : spec.State previous (load + 1)) :
    PeelStep spec previous state :=
  let peeled := spec.peel state
  let options := spec.restorations peeled
  .mk peeled options rfl options.selected rfl options.selected_mem

namespace PeelStep

/-- The selected restoration belongs to the exact options computed from this
peeled predecessor state. -/
theorem selected_from_exact_options {previous : Previous} {load : Nat}
    {state : spec.State previous (load + 1)}
    (step : PeelStep spec previous state) :
    List.Mem step.selected (spec.restorations step.peeled).toList := by
  rw [← step.options_exact]
  exact step.selected_mem

end PeelStep

end Hypostructure.CT12
