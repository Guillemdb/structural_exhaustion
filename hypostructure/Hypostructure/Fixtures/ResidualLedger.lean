import Hypostructure.Core.Residual.Decision
import Hypostructure.Core.Residual.Join

/-!
# Residual-ledger bootstrap fixture

This domain-free fixture checks literal predecessor retention, typed queries,
dependent binary decisions, focused closure, and typed joins.
-/

namespace Hypostructure.Fixtures.ResidualLedger

open Hypostructure.Core.Residual

structure ToyResidual where
  value : Nat
  positive : 0 < value

abbrev RootStage := Ledger ToyResidual

def rootResidual : ToyResidual where
  value := 4
  positive := by decide

def rootStage : RootStage :=
  Ledger.initial rootResidual

def RootPositive (previous : RootStage) : Prop :=
  0 < (residualOf previous).value

def rootPositiveNode : Node RootStage RootPositive :=
  Node.create fun previous => (residualOf previous).positive

abbrev PositiveStage := Ledger.Extension RootStage RootPositive

def positiveStage : PositiveStage :=
  rootPositiveNode.run rootStage

structure Doubled (previous : PositiveStage) where
  value : Nat
  value_eq : value = 2 * (residualOf previous).value

def doubledNode : StageNode PositiveStage Doubled :=
  StageNode.create fun previous => {
    value := 2 * (residualOf previous).value
    value_eq := rfl
  }

abbrev DoubledStage := Ledger.Extension PositiveStage Doubled

def doubledStage : DoubledStage :=
  doubledNode.run positiveStage

/-- The first fact, lifted through the data-bearing second stage. -/
def inheritedPositiveQuery :
    Query DoubledStage
      (fun stage => RootPositive stage.previous.previous) :=
  (Query.latest (Previous := RootStage) (Added := RootPositive)).preserve

def DoubledPositive (previous : DoubledStage) : Prop :=
  0 < previous.added.value

def doubledPositiveNode : Node DoubledStage DoubledPositive :=
  Node.derive inheritedPositiveQuery fun previous positive => by
    unfold DoubledPositive
    rw [previous.added.value_eq]
    exact Nat.mul_pos (by decide) positive

abbrev FinalStage := Ledger.Extension DoubledStage DoubledPositive

def finalStage : FinalStage :=
  doubledPositiveNode.run doubledStage

/-- The root fact remains queryable after two unrelated extensions. -/
def rootFactAtFinalQuery :
    Query FinalStage
      (fun stage => RootPositive stage.previous.previous.previous) :=
  inheritedPositiveQuery.preserve

theorem root_fact_retrieved_at_final : RootPositive rootStage :=
  rootFactAtFinalQuery.read finalStage

theorem prior_query_preserved :
    rootFactAtFinalQuery.read finalStage = positiveStage.added :=
  rfl

theorem literal_three_step_predecessor :
    finalStage.previous.previous.previous = rootStage :=
  rfl

def CanonicalDouble (previous : FinalStage) : Prop :=
  previous.previous.added.value =
    2 * (residualOf previous.previous).value

def NoncanonicalDouble (previous : FinalStage) : Prop :=
  Not (CanonicalDouble previous)

def canonicalDecisionNode :
    Decision.Node FinalStage CanonicalDouble NoncanonicalDouble :=
  Decision.Node.complement CanonicalDouble fun _previous => by
    unfold CanonicalDouble
    infer_instance

abbrev CanonicalDecisionStage :=
  Decision.Stage CanonicalDouble NoncanonicalDouble

def canonicalDecision : CanonicalDecisionStage :=
  canonicalDecisionNode.run finalStage

structure CanonicalOutput (previous : FinalStage)
    (_proof : CanonicalDouble previous) where
  value : Nat
  value_eq : value = previous.previous.added.value

structure NoncanonicalOutput (previous : FinalStage)
    (_proof : NoncanonicalDouble previous) where
  retained : NoncanonicalDouble previous

abbrev AdvancedDecisionStage :=
  Decision.ContinuationStage
    (Yes := CanonicalDouble) (No := NoncanonicalDouble)
    CanonicalOutput NoncanonicalOutput

def advancedDecision : AdvancedDecisionStage :=
  Decision.advance canonicalDecision
    (fun _proof => {
      value := canonicalDecision.previous.previous.added.value
      value_eq := rfl
    })
    (fun proof => { retained := proof })

theorem independent_advancement_retains_decision :
    advancedDecision.previous = canonicalDecision :=
  rfl

/-- The no constructor is impossible for this literal predecessor.  Core
eliminates it and returns a stage indexed only by the retained yes branch. -/
def closedDecision :
    Decision.NoClosedYesStage
      (Yes := CanonicalDouble) (No := NoncanonicalDouble) CanonicalOutput :=
  Decision.closeNoAndContinueYes canonicalDecision
    (fun absent =>
      absent canonicalDecision.previous.previous.added.value_eq)
    (fun _proof => {
      value := canonicalDecision.previous.previous.added.value
      value_eq := rfl
    })

theorem closed_decision_retains_literal_predecessor :
    closedDecision.previous = canonicalDecision :=
  rfl

/-- The root query survives both the decision and its independent branch
advancement. -/
def rootFactAtDecisionQuery :
    Query CanonicalDecisionStage
      (fun stage =>
        RootPositive stage.previous.previous.previous.previous) :=
  rootFactAtFinalQuery.preserve

def rootFactAtAdvancedQuery :
    Query AdvancedDecisionStage
      (fun stage =>
        RootPositive stage.previous.previous.previous.previous.previous) :=
  rootFactAtDecisionQuery.preserve

theorem sibling_fact_retrieved_after_advancement : RootPositive rootStage :=
  rootFactAtAdvancedQuery.read advancedDecision

structure BranchLabel (_previous : FinalStage) where
  label : Bool

def branchLabelNode : StageNode FinalStage BranchLabel :=
  StageNode.create fun _previous => { label := true }

abbrev LabelStage := Ledger.Extension FinalStage BranchLabel

def labelStage : LabelStage :=
  branchLabelNode.run finalStage

def joinSpec :
    Join.Spec ToyResidual AdvancedDecisionStage LabelStage :=
  Join.Spec.sameResidual ToyResidual AdvancedDecisionStage LabelStage

abbrev JoinedStage := Join.Result joinSpec

def joinedStage : JoinedStage :=
  Join.execute joinSpec advancedDecision labelStage rfl

def rootFactAtJoinQuery :
    Query JoinedStage
      (fun joined => RootPositive
        joined.left.previous.previous.previous.previous.previous) :=
  Join.leftQuery rootFactAtAdvancedQuery

def labelAtJoinQuery :
    Query JoinedStage (fun joined => BranchLabel joined.right.previous) :=
  Join.rightQuery
    (Query.latest (Previous := FinalStage) (Added := BranchLabel))

theorem join_preserves_left_query :
    rootFactAtJoinQuery.read joinedStage =
      rootFactAtAdvancedQuery.read advancedDecision :=
  rfl

theorem join_preserves_right_query :
    labelAtJoinQuery.read joinedStage = labelStage.added :=
  rfl

theorem joined_root_fact : RootPositive rootStage :=
  rootFactAtJoinQuery.read joinedStage

theorem joined_residuals_are_exact :
    residualOf joinedStage.left = residualOf joinedStage.right :=
  joinedStage.residual_eq

#print axioms root_fact_retrieved_at_final
#print axioms prior_query_preserved
#print axioms independent_advancement_retains_decision
#print axioms closedDecision
#print axioms sibling_fact_retrieved_after_advancement
#print axioms join_preserves_left_query
#print axioms join_preserves_right_query
#print axioms joined_residuals_are_exact

end Hypostructure.Fixtures.ResidualLedger
