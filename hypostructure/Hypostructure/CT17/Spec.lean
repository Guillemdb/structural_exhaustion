import Hypostructure.Core.Prelude

/-!
# CT17 bounded target-thickening specification

CT17 compares target values with finite blocks at a selected bounded scale or
with a declared orbit slice beyond the finite range.  This file contains only
primitive semantics.  Every finite family and the selected scale itself are
read from the literal predecessor by `Capability`.
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

/-- Domain-neutral target, block, orbit, and compatibility semantics. -/
structure Spec (Previous : Type uPrevious) where
  Target : Previous -> Type uTarget
  Offset : Previous -> Type uOffset
  Position : (previous : Previous) -> Nat -> Type uPosition
  Value : Previous -> Type uValue
  targetValue : (previous : Previous) -> Target previous -> Value previous
  blockValue : (previous : Previous) -> (scale : Nat) ->
    Position previous scale -> Offset previous -> Value previous
  orbitValue : (previous : Previous) -> (scale : Nat) ->
    Offset previous -> Value previous
  Compatible : (previous : Previous) ->
    Target previous -> Offset previous -> Prop

end Hypostructure.CT17
