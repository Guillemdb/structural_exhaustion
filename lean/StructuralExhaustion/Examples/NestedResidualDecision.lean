import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Examples.NestedResidualDecision

open StructuralExhaustion

abbrev Residual := Nat
abbrev Previous (_residual : Residual) := Fin 1
abbrev OuterYes (_residual : Residual) (_previous : Fin 1) : Prop := False
abbrev OuterNo (_residual : Residual) (_previous : Fin 1) : Prop := True
abbrev InnerYes (_residual : Residual) (_previous : Fin 1) : Prop := False
abbrev InnerNo (_residual : Residual) (_previous : Fin 1) : Prop := True
abbrev OuterYesOutput (_residual : Residual) (_previous : Fin 1)
    (_proof : False) := PUnit
abbrev InnerDecision (residual : Residual) (previous : Previous residual)
    (_outerNo : OuterNo residual previous) :=
  Core.ResidualRefinement.State.DependentDecisionAt
    InnerYes InnerNo residual previous

abbrev FirstStage (residual : Residual) :=
  Core.ResidualRefinement.State.DependentDecisionNoAfterYes
    Previous OuterYes OuterNo OuterYesOutput InnerDecision residual

noncomputable def firstNode {facts} :
    Core.ResidualRefinement.State.StageNode (facts := facts) FirstStage where
  produce := fun _state =>
    .noBranch ⟨0, by omega⟩ trivial (.noBranch trivial)

abbrev FinalOutput (_residual : Residual) (_previous : Fin 1)
    (_outerNo : True) (_innerNo : True) := PUnit

abbrev FinalStage (residual : Residual) :=
  Core.ResidualRefinement.State.DependentNestedNoContinuation
    Previous OuterYes OuterNo OuterYesOutput InnerYes InnerNo FinalOutput residual

noncomputable def finalNode {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available FirstStage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) FinalStage :=
  Core.ResidualRefinement.State.StageNode.continueDependentNestedNo
    fun _residual _previous _outerNo _innerNo => ⟨⟩

noncomputable def finalState :=
  finalNode.run (firstNode.run (Core.ResidualRefinement.State.initial 0))

def IsInnerNo {residual : Residual} : FinalStage residual → Prop
  | .innerNoBranch _ _ _ _ => True
  | _ => False

theorem exact_nested_no_leaf_is_retained :
    IsInnerNo (finalState.requireStage (Stage := FinalStage)) := by
  let result := finalState.requireStage (Stage := FinalStage)
  change IsInnerNo result
  cases result with
  | outerYesBranch _ impossible _ => exact False.elim impossible
  | innerYesBranch _ _ impossible => exact False.elim impossible
  | innerNoBranch => trivial

end StructuralExhaustion.Examples.NestedResidualDecision
