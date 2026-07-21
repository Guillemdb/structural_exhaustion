import Hypostructure.PDE.Equation

/-!
# Minimal local PDE models
-/

namespace Hypostructure.PDE

universe u

/--
The mandatory PDE registration.  Targets, observables, coordinates, gauges,
compactness, and budgets are deliberately separate capabilities.
-/
structure LocalModel where
  problem : Core.Problem.{u, u}
  atlas : LocalAtlas problem
  equation : RepresentedEquation problem atlas

/-- Optional public observables with an exact local reflection law. -/
structure ObservableInterface (M : LocalModel.{u}) where
  Index : Type u
  Value : Index -> Type u
  observe : (G : M.problem.Ambient) -> (index : Index) -> Value index
  visible : Index -> M.atlas.Window -> Prop
  localObserve : forall (W : M.atlas.Window), M.atlas.LocalObject W ->
    (index : Index) -> Value index
  localReflect : forall (G : M.problem.Ambient) (W : M.atlas.Window)
      (index : Index), visible index W ->
    localObserve W (M.atlas.restrict G W) index = observe G index

end Hypostructure.PDE
