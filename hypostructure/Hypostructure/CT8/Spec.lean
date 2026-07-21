import Hypostructure.Core.Prelude

/-!
# CT8 finite-repetition specification

CT8 compares occurrences in an ordered predecessor-owned state sequence.  The
specification contains only the semantic classifiers, response evaluator, and
abstract strict-removal relation.  It contains no sequence, finite schedule,
selected pair, route, or execution output.
-/

namespace Hypostructure.CT8

universe uPrevious uState uType uContext uValue uRemoval

/-- Domain-neutral semantics for exact-type repetition and response analysis. -/
structure Spec (Previous : Type uPrevious) where
  State : Previous -> Type uState
  ExactType : Previous -> Type uType
  ResponseContext : Previous -> Type uContext
  ResponseValue : Previous -> Type uValue
  Removal : Previous -> Type uRemoval
  exactType : (previous : Previous) -> State previous -> ExactType previous
  response : (previous : Previous) -> State previous ->
    ResponseContext previous -> ResponseValue previous
  StrictlySmaller : (previous : Previous) -> Removal previous -> Prop

end Hypostructure.CT8
