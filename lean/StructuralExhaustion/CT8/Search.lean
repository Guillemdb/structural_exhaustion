import StructuralExhaustion.CT8.State

namespace StructuralExhaustion.CT8

universe uAmbient uBranch uState uType uResponseContext
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uType, uResponseContext} P)

inductive RepetitionDecision (sequence : List capability.State) where
  | repeated (pair : OrderedRepeatedPair capability sequence)
  | unique (absent : OrderedRepeatedPair capability sequence → False)

def sameTypeDecidable (first second : capability.State) :
    Decidable (capability.exactType first = capability.exactType second) :=
  capability.exactTypes.decEq _ _

/-- Deterministically find the first left endpoint whose tail contains an
equal exact type, then the first matching right endpoint. -/
def findRepeated : (sequence : List capability.State) →
    RepetitionDecision capability sequence
  | [] => .unique fun pair => by cases pair
  | first :: tail =>
      match Core.FiniteSearch.onList tail
          (fun second => capability.exactType first = capability.exactType second)
          (sameTypeDecidable capability first) with
      | .found second member sameType => .repeated (.here second member sameType)
      | .absent noHere =>
          match findRepeated tail with
          | .repeated pair => .repeated (.later pair)
          | .unique noLater => .unique fun pair => by
              cases pair with
              | here second member sameType => exact noHere second member sameType
              | later pair => exact noLater pair

variable (ctx : Core.BranchContext P)
variable (input : Input capability ctx)

inductive ResponseDecision (pair : OrderedRepeatedPair capability input.sequence) where
  | removable (residual : RemovalResidual capability ctx input)
  | separating (residual : SeparationResidual capability ctx input)

def analyzeResponses (pair : OrderedRepeatedPair capability input.sequence) :
    ResponseDecision capability ctx input pair :=
  match Core.FiniteSearch.search capability.responseContexts
      (fun context => capability.response pair.first context ≠
        capability.response pair.second context)
      (fun _ => inferInstance) with
  | .found context differs => .separating ⟨pair, ⟨context, differs⟩⟩
  | .absent noDifference =>
      have equal : ResponsesEqual capability ctx input pair := fun context =>
        match decEq (capability.response pair.first context)
          (capability.response pair.second context) with
        | .isTrue same => same
        | .isFalse differs => (noDifference context differs).elim
      .removable {
        pair := pair
        responsesEqual := equal
        smaller := input.remove pair.first pair.second
        exact := rfl
      }

theorem findRepeated_sound (sequence : List capability.State) :
    match findRepeated capability sequence with
    | .repeated pair => capability.exactType pair.first = capability.exactType pair.second
    | .unique _ => OrderedRepeatedPair capability sequence → False := by
  cases findRepeated capability sequence with
  | repeated pair => exact pair.typesEqual
  | unique absent => exact absent

theorem analyzeResponses_sound (pair : OrderedRepeatedPair capability input.sequence) :
    match analyzeResponses capability ctx input pair with
    | .removable residual => ResponsesEqual capability ctx input residual.pair
    | .separating residual =>
        capability.response residual.pair.first residual.separator.context ≠
          capability.response residual.pair.second residual.separator.context := by
  cases analyzeResponses capability ctx input pair with
  | removable residual => exact residual.responsesEqual
  | separating residual => exact residual.separator.differs

end StructuralExhaustion.CT8
