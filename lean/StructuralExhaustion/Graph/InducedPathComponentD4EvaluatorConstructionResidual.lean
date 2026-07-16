import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual

namespace StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual

universe u

/-! Construction inputs still missing after the D4 evaluator contract. -/

inductive ConstructionInput
  | componentLocalData
  | graphOwnedPredicateDefinition
  | predicateDerivation
  deriving DecidableEq, Repr

def constructionInputs : List ConstructionInput :=
  [.componentLocalData, .graphOwnedPredicateDefinition, .predicateDerivation]

theorem constructionInputs_nodup : constructionInputs.Nodup := by decide

/-- A typed construction residual.  It preserves the exact evaluator residual
and adds only an obligation list; it contains no Boolean or evaluator. -/
structure Residual {Marker : Type u} {source : Nonempty Marker}
    {ledger : InducedPathComponentD4D7ClauseSchedule.Ledger source}
    {focused : InducedPathComponentD4D7ClauseCursor.Cursor ledger}
    {request : InducedPathComponentD4LocalClauseRequest.Request focused}
    (pending : InducedPathComponentD4EvaluatorResidual.Residual request) where
  predecessor : InducedPathComponentD4EvaluatorResidual.Residual request
  predecessorExact : predecessor = pending
  inputs : List ConstructionInput
  inputsExact : inputs = constructionInputs
  inputsNodup : inputs.Nodup

def residual {Marker : Type u} {source : Nonempty Marker}
    {ledger : InducedPathComponentD4D7ClauseSchedule.Ledger source}
    {focused : InducedPathComponentD4D7ClauseCursor.Cursor ledger}
    {request : InducedPathComponentD4LocalClauseRequest.Request focused}
    (pending : InducedPathComponentD4EvaluatorResidual.Residual request) :
    Residual pending where
  predecessor := pending
  predecessorExact := rfl
  inputs := constructionInputs
  inputsExact := rfl
  inputsNodup := constructionInputs_nodup

@[simp] theorem residual_inputs_length {Marker : Type u}
    {source : Nonempty Marker}
    {ledger : InducedPathComponentD4D7ClauseSchedule.Ledger source}
    {focused : InducedPathComponentD4D7ClauseCursor.Cursor ledger}
    {request : InducedPathComponentD4LocalClauseRequest.Request focused}
    (pending : InducedPathComponentD4EvaluatorResidual.Residual request) :
    (residual pending).inputs.length = 3 := rfl

end StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual
