import Hypostructure.Core.Finite.Enumeration

/-!
# CT16 whole-support specification

CT16 inspects one explicit coordinate family already owned by its incoming
residual.  Closed codes are computed directly from the literal predecessor;
there is no family of candidate codes.
-/

namespace Hypostructure.CT16

universe uPrevious uCoordinate uCode

/-- Domain-neutral whole-support and closed-code semantics.

`closedCode` is the mathematical denotation.  Executable CT16 capabilities must
register a counted implementation, prove that its value equals this denotation,
and supply its exact polynomial work budget. -/
structure Spec (Previous : Type uPrevious) where
  Coordinate : Previous -> Type uCoordinate
  InSupport : (previous : Previous) -> Coordinate previous -> Prop
  ClosedCode : Previous -> Type uCode
  closedCode : (previous : Previous) -> ClosedCode previous
  targetCode : (previous : Previous) -> ClosedCode previous

/-- Every coordinate in the exact incoming schedule belongs to the support. -/
def WholeSupport {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (previous : Previous)
    (coordinates : Core.Finite.Enumeration (spec.Coordinate previous)) : Prop :=
  forall coordinate, coordinate ∈ coordinates.values ->
    spec.InSupport previous coordinate

/-- Whole support whose directly computed code is literally the target code. -/
def ExactClosedType {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uCoordinate, uCode} Previous)
    (previous : Previous)
    (coordinates : Core.Finite.Enumeration (spec.Coordinate previous)) : Prop :=
  WholeSupport spec previous coordinates ∧
    spec.closedCode previous = spec.targetCode previous

end Hypostructure.CT16
