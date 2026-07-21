import Hypostructure.PDE.Observable

/-!
# External PDE targets

A target remains an external predicate.  Its interface says exactly how the
target is read from public observables.  Representation invariance is then a
framework theorem, rather than a second application-supplied law.
-/

namespace Hypostructure.PDE

universe u

/-- Observable characterization of one external theorem target. -/
structure TargetInterface (M : LocalModel.{u})
    (Target : M.problem.Ambient -> Prop)
    (observables : ObservableInterface M) where
  accepts : ((index : observables.Index) -> observables.Value index) -> Prop
  target_iff : forall object,
    Target object <-> accepts (fun index => observables.observe object index)

namespace TargetInterface

/-- Derive Core target transport from observable representation invariance. -/
def coreInvariant {M : LocalModel.{u}}
    {Target : M.problem.Ambient -> Prop}
    {observables : ObservableInterface M}
    {semantics : RepresentationSemantics M.problem}
    (interface : TargetInterface M Target observables)
    (observableInvariant : ObservableInvariant M semantics observables) :
    Core.TargetInvariant semantics Target where
  target_iff := by
    intro left right equivalent
    rw [interface.target_iff left, interface.target_iff right]
    rw [observableInvariant.vector_eq equivalent]

end TargetInterface

end Hypostructure.PDE
