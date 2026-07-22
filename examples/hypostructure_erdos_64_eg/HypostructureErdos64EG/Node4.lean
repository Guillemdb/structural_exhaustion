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

/-- Node 4 retrieves both inherited inputs through one active query. -/
def node4InputQuery :=
  node2CounterexampleQuery.and
    (Core.Residual.Focus.ActiveQuery.ofQuery node1ResidualAtNode2Query)

/-- Node 4 uses the Core-owned selector for the node-2 positive branch. -/
def node4WorkBudget :
    Core.PolynomialCheckBudget Node2Stage.{u} :=
  CounterexampleFocus.selectionBudget

/-- Node 4's sole new payload on the focused branch. -/
abbrev Node4Output (_stage : Node2Stage.{u})
    (_active : CounterexampleFocus.Active _stage) :=
  Core.MinimalCounterexampleContext problem Target EGProgress

/-- Exact accumulated stage after node 4. -/
abbrev Node4Stage :=
  Core.Residual.Focus.Stage CounterexampleFocus Node4Output

/-- Counted node-4 execution, including the inactive node-3 sibling. -/
noncomputable def node4Counted (previous : Node2Stage.{u}) :
    Core.Counted Node4Stage.{u} :=
  Core.Residual.Focus.runCounted CounterexampleFocus
    (Output := Node4Output) previous
    fun active _checks _exact =>
    let inputs := node4InputQuery.read previous active
    Graph.selectLexicographicMinimal
      (Baseline := Baseline) (BranchState := BranchState) (Target := Target)
      inputs.snd.object inputs.snd.baseline inputs.fst.2 (fun _current => ())

/-- Execute minimal-counterexample selection on the exact focused branch. -/
noncomputable def node4 (previous : Node2Stage.{u}) : Node4Stage.{u} :=
  (node4Counted previous).value

/-- Focus inherited by every downstream counterexample node. -/
abbrev Node4Focus :=
  Core.Residual.Focus.successor CounterexampleFocus Node4Output

/-- Typed ledger query for the selected minimal context. -/
def node4ContextQuery :
    Core.Residual.Focus.ActiveQuery Node4Focus
      (fun stage active => Node4Output stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

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
  rw [node4Counted, Core.Residual.Focus.runCounted_checks]
  rfl

theorem node4Counted_work_bounded (previous : Node2Stage.{u}) :
    (node4Counted previous).checks <=
      node4WorkBudget.coefficient *
        (node4WorkBudget.size previous + 1) ^
          node4WorkBudget.degree :=
  Core.Residual.Focus.runCounted_checks_bounded CounterexampleFocus previous _

/-- Proof-relevant audit record for node-4 focused minimal selection. -/
def node4Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node2Stage.{u} Node2Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node4", "node4Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node4", "node4InputQuery"⟩,
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
    ⟨"Hypostructure.Core.Residual.Focus", "Focus.runCounted"⟩,
    ⟨"Hypostructure.Graph.Progress", "selectLexicographicMinimal"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Focus", "Focus.Outcome"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Core.Residual.Ledger", "Ledger.extend"⟩,
      .residualStage⟩,
    ⟨⟨"Hypostructure.Graph.Progress", "selectLexicographicMinimal"⟩,
      .searchResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Residual.Focus", "Focus.runCounted_checks"⟩,
    ⟨"Hypostructure.Core.Residual.Focus",
      "Focus.runCounted_checks_bounded"⟩
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
    node4Metadata.workBound.checks previous <=
      node4Metadata.workBound.coefficient *
        (node4Metadata.workBound.size previous + 1) ^
          node4Metadata.workBound.degree :=
  node4MetadataComplete.work_bounded previous

#print axioms node4
#print axioms node4ContextQuery_minimal
#print axioms node4Counted_checks_eq_one
#print axioms node4Counted_work_bounded
#print axioms node4_metadata_has_no_manual_obligation
#print axioms node4_metadata_work_bounded

end HypostructureErdos64EG
