import Hypostructure.Core.Assembly.Locality

/-!
# Local PDE atlases

This file specializes Core locality with points and nested core/work windows.
Targets remain external to a model.
-/

namespace Hypostructure.PDE

universe u

/-- A theorem target over a problem.  Targets are not fields of a local model. -/
abbrev Target (P : Core.Problem.{u, u}) := P.Ambient -> Prop

/--
Local windows, their nesting relation, and exact restriction.  Local objects
may depend on the window, so restriction cannot silently change its domain.
-/
structure LocalAtlas (P : Core.Problem.{u, u}) where
  Point : Type u
  Window : Type u
  contains : Point -> Window -> Prop
  nested : Window -> Window -> Prop
  nested_refl : forall W, nested W W
  nested_trans : forall {U V W}, nested U V -> nested V W -> nested U W
  core : Window -> Window
  core_nested : forall W, nested (core W) W
  LocalObject : Window -> Type u
  restrict : P.Ambient -> (W : Window) -> LocalObject W
  restrictLocal : forall {U V}, nested U V -> LocalObject V -> LocalObject U
  restrict_refl : forall (W) (u : LocalObject W),
    restrictLocal (nested_refl W) u = u
  restrict_trans : forall {U V W} (hUV : nested U V) (hVW : nested V W)
      (u : LocalObject W),
    restrictLocal hUV (restrictLocal hVW u) =
      restrictLocal (nested_trans hUV hVW) u
  restrict_global : forall (G : P.Ambient) {U V} (h : nested U V),
    restrictLocal h (restrict G V) = restrict G U

namespace LocalAtlas

/-- Forget the PDE point/core data and expose the domain-independent locality. -/
def toCoreLocality {P : Core.Problem.{u, u}} (A : LocalAtlas P) :
    Core.Locality P where
  Window := A.Window
  nested := A.nested
  nestedRefl := A.nested_refl
  nestedTrans := A.nested_trans
  LocalObject := A.LocalObject
  restrict := A.restrict
  restrictNested := A.restrictLocal
  restrictNested_eq := by
    intro core work contained object
    exact A.restrict_global object contained

/-- Restrict an ambient object first to a work window and then to its core. -/
def restrictCore {P : Core.Problem.{u, u}} (A : LocalAtlas P) (G : P.Ambient)
    (W : A.Window) : A.LocalObject (A.core W) :=
  A.restrictLocal (A.core_nested W) (A.restrict G W)

@[simp]
theorem restrictCore_eq {P : Core.Problem.{u, u}} (A : LocalAtlas P)
    (G : P.Ambient) (W : A.Window) :
    A.restrictCore G W = A.restrict G (A.core W) :=
  A.restrict_global G (A.core_nested W)

end LocalAtlas

/--
Optional pointwise covering data.  It chooses one window only for a supplied
relevant point and never enumerates the ambient point space.
-/
structure CoveringProfile (P : Core.Problem.{u, u}) (A : LocalAtlas P) where
  relevant : P.Ambient -> A.Point -> Prop
  window : forall (G : P.Ambient) (x : A.Point), relevant G x -> A.Window
  contains_point : forall (G : P.Ambient) (x : A.Point)
      (hx : relevant G x), A.contains x (window G x hx)

end Hypostructure.PDE
