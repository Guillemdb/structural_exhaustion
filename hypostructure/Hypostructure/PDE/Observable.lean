import Hypostructure.PDE.Representation

/-!
# Represented PDE observables

`ObservableInterface` is intentionally defined by the minimal local model
module.  This file adds the optional representation-invariance certificate
needed by target registration.  It does not make observables mandatory data of
`LocalModel` and it does not enumerate an implicit observable family.
-/

namespace Hypostructure.PDE

universe u

/-- Public observables depend only on the represented object, not on a chosen
ambient representative. -/
structure ObservableInvariant (M : LocalModel.{u})
    (semantics : RepresentationSemantics M.problem)
    (observables : ObservableInterface M) : Prop where
  observe_eq : forall {left right : M.problem.Ambient},
    semantics.equivalent left right ->
      forall index, observables.observe left index =
        observables.observe right index

namespace ObservableInvariant

/-- Equality semantics makes every observable family representation-invariant. -/
def equality (M : LocalModel.{u}) (observables : ObservableInterface M) :
    ObservableInvariant M (RepresentationSemantics.equality M.problem)
      observables where
  observe_eq := by
    intro left right equivalent index
    cases equivalent
    rfl

/-- Equality of the complete dependent observable vectors. -/
theorem vector_eq {M : LocalModel.{u}}
    {semantics : RepresentationSemantics M.problem}
    {observables : ObservableInterface M}
    (invariant : ObservableInvariant M semantics observables)
    {left right : M.problem.Ambient}
    (equivalent : semantics.equivalent left right) :
    (fun index => observables.observe left index) =
      fun index => observables.observe right index := by
  funext index
  exact invariant.observe_eq equivalent index

end ObservableInvariant

end Hypostructure.PDE
