import HypostructureErdos64EG.Node63
import HypostructureErdos64EG.Node64
import Hypostructure.Graph.Strategy

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-! The EG layer supplies only continuation strategies.  Core receives the
complete predecessor stage and owns the dichotomy routing and ledger growth. -/

structure TypeAStrategyContract (Previous : Type u)
    (node62Contract : Node62Contract Previous) where
  strategy : (stage : Node62Stage node62Contract) ->
    Node62NoHighSurplus node62Contract stage.previous ->
    Core.Strategy.Contract.{u, 0, u} (Node62Stage node62Contract)

structure TypeBStrategyContract (Previous : Type u)
    (node62Contract : Node62Contract Previous) where
  strategy : (stage : Node62Stage node62Contract) ->
    Node62HighSurplus node62Contract stage.previous ->
    Core.Strategy.Contract.{u, 0, u} (Node62Stage node62Contract)

structure TypeABStrategyContract (Previous : Type u)
    (node62Contract : Node62Contract Previous) where
  typeA : TypeAStrategyContract Previous node62Contract
  typeB : TypeBStrategyContract Previous node62Contract

def combineTypeAB
    (typeA : TypeAStrategyContract Previous node62Contract)
    (typeB : TypeBStrategyContract Previous node62Contract) :
    TypeABStrategyContract Previous node62Contract where
  typeA := typeA
  typeB := typeB

noncomputable def typeABDichotomy
    (contract : TypeABStrategyContract Previous node62Contract) :
    Core.Strategy.Dichotomy (Node62Stage node62Contract) where
  LeftPayload stage := Core.Strategy.ProofPayload
    (Node62NoHighSurplus node62Contract stage.previous)
  RightPayload stage := Core.Strategy.ProofPayload
    (Node62HighSurplus node62Contract stage.previous)
  classify stage := match stage.added with
    | .yesBranch high => Sum.inr ⟨high⟩
    | .noBranch noHigh => Sum.inl ⟨noHigh⟩

abbrev TypeABStage (contract : TypeABStrategyContract Previous node62Contract)
    (stage : Node62Stage node62Contract) :=
  Core.Residual.Ledger.Extension (Node62Stage node62Contract) (fun previous =>
    Sum
      (Core.Strategy.RoutedLeft (typeABDichotomy contract)
        (fun stage witness => contract.typeA.strategy stage witness.down) previous)
      (Core.Strategy.RoutedRight (typeABDichotomy contract)
        (fun stage witness => contract.typeB.strategy stage witness.down) previous))

noncomputable def runTypeAB
    (contract : TypeABStrategyContract Previous node62Contract)
    (stage : Node62Stage node62Contract) : TypeABStage contract stage :=
  Core.Strategy.runRouted (typeABDichotomy contract)
    (fun previous witness => contract.typeA.strategy previous witness.down)
    (fun previous witness => contract.typeB.strategy previous witness.down) stage

@[simp] theorem runTypeAB_previous
    (contract : TypeABStrategyContract Previous node62Contract)
    (stage : Node62Stage node62Contract) :
    (runTypeAB contract stage).previous = stage := by
  exact Core.Strategy.runRouted_previous
    (typeABDichotomy contract)
    (fun previous witness => contract.typeA.strategy previous witness.down)
    (fun previous witness => contract.typeB.strategy previous witness.down)
    stage

end HypostructureErdos64EG
