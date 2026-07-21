import Hypostructure.PDE.Atlas

/-!
# Represented local equations

Equation data and satisfaction are separate: data records the chosen
representation, while `satisfies` is its mathematical equation contract.
-/

namespace Hypostructure.PDE

universe u

/-- A local equation whose representation and validity restrict exactly. -/
structure RepresentedEquation (P : Core.Problem.{u, u}) (A : LocalAtlas P) where
  EquationData : (W : A.Window) -> A.LocalObject W -> Type u
  satisfies : forall {W : A.Window} {u : A.LocalObject W},
    EquationData W u -> Prop
  restrictEquation : forall {U V : A.Window} (h : A.nested U V)
      {u : A.LocalObject V},
    EquationData V u -> EquationData U (A.restrictLocal h u)
  restrict_satisfies : forall {U V : A.Window} (h : A.nested U V)
      {u : A.LocalObject V} (data : EquationData V u),
    satisfies data -> satisfies (restrictEquation h data)

/-- A local object together with represented equation data and its proof. -/
structure EquationState {P : Core.Problem.{u, u}} {A : LocalAtlas P}
    (E : RepresentedEquation P A) (W : A.Window) where
  object : A.LocalObject W
  data : E.EquationData W object
  valid : E.satisfies data

namespace EquationState

/-- Restriction of a valid represented equation state to a nested window. -/
def restrict {P : Core.Problem.{u, u}} {A : LocalAtlas P}
    {E : RepresentedEquation P A} {U V : A.Window} (h : A.nested U V)
    (state : EquationState E V) : EquationState E U where
  object := A.restrictLocal h state.object
  data := E.restrictEquation h state.data
  valid := E.restrict_satisfies h state.data state.valid

@[simp]
theorem restrict_object {P : Core.Problem.{u, u}} {A : LocalAtlas P}
    {E : RepresentedEquation P A} {U V : A.Window} (h : A.nested U V)
    (state : EquationState E V) :
    (state.restrict h).object = A.restrictLocal h state.object := rfl

end EquationState

end Hypostructure.PDE
