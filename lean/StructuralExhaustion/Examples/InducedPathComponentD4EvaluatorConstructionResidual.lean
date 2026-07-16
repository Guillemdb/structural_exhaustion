import StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual

namespace StructuralExhaustion.Examples.ComponentD4EvaluatorConstructionResidual

open StructuralExhaustion.Graph

example {Marker : Type} (marker : Nonempty Marker) :
    let ledger := InducedPathComponentD4D7ClauseSchedule.ledger marker
    let cursor := InducedPathComponentD4D7ClauseCursor.cursor ledger
    let request := InducedPathComponentD4LocalClauseRequest.request cursor
    let evaluator := InducedPathComponentD4EvaluatorResidual.residual request
    let construction :=
      InducedPathComponentD4EvaluatorConstructionResidual.residual evaluator
    construction.predecessor = evaluator ∧ construction.inputs =
      [.componentLocalData, .graphOwnedPredicateDefinition,
        .predicateDerivation] := by
  simp [InducedPathComponentD4EvaluatorConstructionResidual.residual,
    InducedPathComponentD4EvaluatorConstructionResidual.constructionInputs]

end StructuralExhaustion.Examples.ComponentD4EvaluatorConstructionResidual
