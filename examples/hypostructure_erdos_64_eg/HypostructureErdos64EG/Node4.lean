import Hypostructure.Graph.Progress
import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Focus
import HypostructureErdos64EG.Contract
import HypostructureErdos64EG.Node2

/-!
# Diagram node 4: lexicographically minimal counterexample

Node 4 opens Core's repeatable focus on node 2's exact counterexample
constructor. Core performs well-founded selection and leaves the terminal
node-3 sibling inactive without manufacturing a payload for it.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Core-generated focus on node 2's counterexample constructor. -/
abbrev CounterexampleFocus :=
  Core.Residual.Focus.yes
    (Yes := IsCounterexample) (No := IsNotCounterexample)

/-- Exact counterexample proof selected by node 2. -/
def node2CounterexampleQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun stage _active => IsCounterexample stage.previous) :=
  Core.Residual.Focus.yesProof

/-- Root data lifted through node 2's literal decision extension. -/
def node1ResidualAtNode2Query :
    Core.Residual.Query Node2Stage (fun _stage => InitialResidual.{u}) :=
  node1ResidualQuery.preserve

/-- Root residual read on the exact counterexample branch. -/
def node4RootResidualQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun _stage _active => InitialResidual.{u}) :=
  Core.Residual.Focus.ActiveQuery.ofQuery node1ResidualAtNode2Query

/-- Current graph read from the predecessor-owned root residual. -/
def node4ObjectQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun _stage _active => Graph.FiniteObject.{u}) :=
  egInitialObjectActiveQuery CounterexampleFocus node4RootResidualQuery

/-- Baseline proof read from the predecessor-owned root residual. -/
def node4BaselineQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun stage active => Baseline (node4ObjectQuery.read stage active)) :=
  egInitialBaselineActiveQuery CounterexampleFocus node4RootResidualQuery

/-- Target avoidance read from node 2's exact counterexample branch. -/
def node4AvoidsQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun stage active => Not (Target (node4ObjectQuery.read stage active))) :=
  egCounterexampleAvoidsActiveQuery CounterexampleFocus
    node4RootResidualQuery node2CounterexampleQuery

/-- Node 4 uses the Core-owned selector for the node-2 positive branch. -/
def node4WorkBudget :
    Core.PolynomialCheckBudget Node2Stage.{u} :=
  CounterexampleFocus.selectionBudget

/-- Node 4's sole new payload on the focused branch. -/
abbrev Node4Output (stage : Node2Stage.{u})
    (active : CounterexampleFocus.Active stage) :=
  Graph.FocusedLexicographicMinimalOutput CounterexampleFocus
    (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery stage active

/-- Exact accumulated stage after node 4. -/
abbrev Node4Stage :=
  Graph.FocusedLexicographicMinimalStage CounterexampleFocus
    (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery

/-- Counted node-4 execution, including the inactive node-3 sibling. -/
noncomputable def node4Counted (previous : Node2Stage.{u}) :
    Core.Counted Node4Stage.{u} :=
  Graph.executeFocusedLexicographicMinimalCounted CounterexampleFocus
    (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery
    (fun _current => ()) previous

/-- Execute minimal-counterexample selection on the exact focused branch. -/
noncomputable def node4 (previous : Node2Stage.{u}) : Node4Stage.{u} :=
  (node4Counted previous).value

/-- Focus inherited by every downstream counterexample node. -/
abbrev Node4Focus :=
  Graph.FocusedLexicographicMinimalProfile CounterexampleFocus
    (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery

/-- Typed ledger query for the selected minimal context. -/
def node4ContextQuery :
    Core.Residual.Focus.ActiveQuery Node4Focus
      (fun stage active => Node4Output stage.previous active) :=
  Graph.focusedLexicographicMinimalContextQuery CounterexampleFocus
    (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery

/-- The context selected at node 4 carries the registered Core minimality
kernel for lexicographic graph progress. -/
theorem node4ContextQuery_minimal (stage : Node4Stage.{u})
    (active : Node4Focus.Active stage) :
    Core.MinimalityKernel problem Target EGProgress
      (node4ContextQuery.read stage active).toBranchContext :=
  (node4ContextQuery.read stage active).minimal

@[simp] theorem node4_previous (previous : Node2Stage.{u}) :
    (node4 previous).previous = previous :=
  rfl

@[simp] theorem node4Counted_checks_eq_one (previous : Node2Stage.{u}) :
    (node4Counted previous).checks = 1 := by
  rw [node4Counted, Graph.executeFocusedLexicographicMinimalCounted_checks]
  rfl

theorem node4Counted_work_bounded (previous : Node2Stage.{u}) :
    node4WorkBudget.Within previous (node4Counted previous).checks :=
  Graph.executeFocusedLexicographicMinimalCounted_work_within
    CounterexampleFocus (BranchState := BranchState)
    node4ObjectQuery node4BaselineQuery node4AvoidsQuery
    (fun _current => ()) previous

/-- Proof-relevant audit record for node-4 focused minimal selection. -/
def node4Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node2Stage.{u} Node2Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node4", "node4Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node4", "node4ObjectQuery"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node2", "node2"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node4", "node2CounterexampleQuery"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node4", "node1ResidualAtNode2Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node4", "node1ResidualAtNode2Query"⟩
    Result := fun _stage => InitialResidual.{u}
    query := node1ResidualAtNode2Query
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.Progress",
      "executeFocusedLexicographicMinimalCounted"⟩,
    ⟨"Hypostructure.Graph.Progress",
      "focusedLexicographicMinimalContextQuery"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "Focus.Outcome"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.Progress",
      "FocusedLexicographicMinimalStage"⟩,
      .residualStage⟩,
    ⟨⟨"Hypostructure.Graph.Progress", "selectLexicographicMinimal"⟩,
      .searchResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.Progress",
      "executeFocusedLexicographicMinimalCounted_checks"⟩,
    ⟨"Hypostructure.Graph.Progress",
      "executeFocusedLexicographicMinimalCounted_work_within"⟩
  ]
  workBound := node4WorkBudget
  manualObligations := []

/-- Node 4 has no unrecorded mathematical or routing obligation. -/
def node4MetadataComplete :
    Core.Metadata.Complete node4Metadata :=
  ⟨rfl⟩

theorem node4_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node4Metadata.manualObligations) :=
  node4MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same one-check branch-selection budget used by
the counted run. -/
theorem node4_metadata_work_bounded (previous : Node2Stage.{u}) :
    node4Metadata.workBound.Within previous
      (node4Metadata.workBound.checks previous) :=
  node4MetadataComplete.work_within previous

#print axioms node4
#print axioms node4ContextQuery_minimal
#print axioms node4Counted_checks_eq_one
#print axioms node4Counted_work_bounded
#print axioms node4_metadata_has_no_manual_obligation
#print axioms node4_metadata_work_bounded

end HypostructureErdos64EG
