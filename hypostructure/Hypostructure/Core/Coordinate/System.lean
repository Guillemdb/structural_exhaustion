import Hypostructure.Core.Problem

/-!
# Domain-independent coordinate systems

A domain registers only primitive coordinate actions. Core owns path
construction, execution, and all composite transports.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uCoordinate uObject uPrimitive

/-- A family of represented objects and primitive coordinate actions. -/
structure CoordinateSystem (P : Problem.{uAmbient, uBranch}) where
  Coordinate : Type uCoordinate
  Object : Coordinate -> Type uObject
  realize : (coordinate : Coordinate) -> Object coordinate -> P.Ambient
  Primitive : Coordinate -> Coordinate -> Type uPrimitive
  act : {source target : Coordinate} ->
    Primitive source target -> Object source -> Object target

end Hypostructure.Core
