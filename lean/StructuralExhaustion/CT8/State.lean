import StructuralExhaustion.CT8.Capability

namespace StructuralExhaustion.CT8

universe uAmbient uBranch uState uType uResponseContext

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)
variable (ctx : Core.BranchContext P)
variable (input : Input capability ctx)

/-- Two occurrences in strict left-to-right sequence order with equal exact
types.  The constructors encode positions, so equal values at distinct
occurrences remain detectable. -/
inductive OrderedRepeatedPair : List capability.State → Type _ where
  | here {first : capability.State} {tail : List capability.State}
      (second : capability.State) (member : second ∈ tail)
      (sameType : capability.exactType first = capability.exactType second) :
      OrderedRepeatedPair (first :: tail)
  | later {head : capability.State} {tail : List capability.State}
      (pair : OrderedRepeatedPair tail) : OrderedRepeatedPair (head :: tail)

namespace OrderedRepeatedPair

def first {sequence} : OrderedRepeatedPair capability sequence → capability.State
  | .here (first := first) _ _ _ => first
  | .later pair => pair.first

def second {sequence} : OrderedRepeatedPair capability sequence → capability.State
  | .here second _ _ => second
  | .later pair => pair.second

theorem typesEqual {sequence} (pair : OrderedRepeatedPair capability sequence) :
    capability.exactType pair.first = capability.exactType pair.second := by
  induction pair with
  | here second member sameType => exact sameType
  | later pair ih => exact ih

end OrderedRepeatedPair

structure NoRepetitionCertificate : Prop where
  absent : OrderedRepeatedPair capability input.sequence → False

def ResponsesEqual (pair : OrderedRepeatedPair capability input.sequence) : Prop :=
  ∀ context : capability.ResponseContext,
    capability.response pair.first context = capability.response pair.second context

structure ResponseSeparator (pair : OrderedRepeatedPair capability input.sequence) where
  context : capability.ResponseContext
  differs : capability.response pair.first context ≠ capability.response pair.second context

structure RemovalResidual where
  pair : OrderedRepeatedPair capability input.sequence
  responsesEqual : ResponsesEqual capability ctx input pair
  smaller : Core.SmallerObject P ctx.G
  exact : smaller = input.remove pair.first pair.second

structure SeparationResidual where
  pair : OrderedRepeatedPair capability input.sequence
  separator : ResponseSeparator capability ctx input pair

end StructuralExhaustion.CT8
