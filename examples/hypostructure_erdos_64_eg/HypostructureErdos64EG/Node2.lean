import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Decision
import HypostructureErdos64EG.Node1

/-!
# Diagram node 2: exhaustive counterexample decision

The minimum-degree premise is already in the root residual.  Node 2 asks the
paper's exact question and lets Core construct both dependent branches.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Framework query for the unique residual carried by node 1. -/
def node1ResidualQuery :
    Core.Residual.Query Node1Stage (fun _stage => InitialResidual.{u}) :=
  Core.Residual.Query.residual

/-- The exact positive branch of diagram node 2. -/
def IsCounterexample (stage : Node1Stage.{u}) : Prop :=
  let residual := node1ResidualQuery.read stage
  problem.Baseline residual.object ∧ Not (Target residual.object)

/-- The exact negative branch of diagram node 2. -/
def IsNotCounterexample (stage : Node1Stage.{u}) : Prop :=
  Target (node1ResidualQuery.read stage).object

/-- Core-owned exhaustive decision profile for node 2. -/
noncomputable def node2Decision :
    Core.Residual.Decision.Node Node1Stage IsCounterexample
      IsNotCounterexample :=
  Core.Residual.Decision.Node.create
    (fun stage => by
      classical
      exact inferInstanceAs (Decidable (IsCounterexample stage)))
    (fun stage absent => by
      let residual := node1ResidualQuery.read stage
      change Target residual.object
      by_contra avoids
      exact absent ⟨residual.baseline, avoids⟩)

/-- Exact accumulated stage emitted by diagram node 2. -/
abbrev Node2Stage :=
  Core.Residual.Decision.Stage IsCounterexample IsNotCounterexample

/-- Node 2 performs one framework-owned binary branch inspection. -/
def node2WorkBudget :
    Core.PolynomialCheckBudget Node1Stage.{u} :=
  Core.PolynomialCheckBudget.constant (fun _previous => 0) 1

/-- Counted execution of the exact Core decision on its node-1 predecessor. -/
noncomputable def node2Counted (previous : Node1Stage.{u}) :
    Core.Counted Node2Stage.{u} :=
  ⟨node2Decision.run previous, 1⟩

/-- Execute node 2 on its literal node-1 predecessor. -/
noncomputable def node2 (previous : Node1Stage.{u}) : Node2Stage.{u} :=
  (node2Counted previous).value

@[simp] theorem node2Counted_value (previous : Node1Stage.{u}) :
    (node2Counted previous).value = node2 previous :=
  rfl

@[simp] theorem node2_previous (previous : Node1Stage.{u}) :
    (node2 previous).previous = previous :=
  rfl

/-- Node 2 exposes exactly the two branches in the manuscript. -/
theorem node2_exhaustive (previous : Node1Stage.{u}) :
    match (node2 previous).added with
    | .yesBranch _proof => IsCounterexample previous
    | .noBranch _proof => IsNotCounterexample previous := by
  cases (node2 previous).added with
  | yesBranch proof => exact proof
  | noBranch proof => exact proof

/-- A target certificate forces the exact negative constructor. -/
theorem node2_no_branch_of_target (previous : Node1Stage.{u})
    (target : IsNotCounterexample previous) :
    ∃ proof : IsNotCounterexample previous,
      (node2 previous).added =
        Core.Residual.Decision.Binary.noBranch proof := by
  unfold node2 node2Counted Core.Residual.Decision.Node.run
  cases decision : node2Decision.yesDecidable previous with
  | isTrue counterexample =>
      exact (counterexample.2 target).elim
  | isFalse absent =>
      exact ⟨node2Decision.no_of_not_yes previous absent, rfl⟩

/-- A counterexample certificate forces the exact positive constructor. -/
theorem node2_yes_branch_of_counterexample (previous : Node1Stage.{u})
    (counterexample : IsCounterexample previous) :
    ∃ proof : IsCounterexample previous,
      (node2 previous).added =
        Core.Residual.Decision.Binary.yesBranch proof := by
  unfold node2 node2Counted Core.Residual.Decision.Node.run
  cases decision : node2Decision.yesDecidable previous with
  | isTrue proof =>
      exact ⟨proof, rfl⟩
  | isFalse absent =>
      exact (absent counterexample).elim

@[simp] theorem node2Counted_checks_eq_one (previous : Node1Stage.{u}) :
    (node2Counted previous).checks = 1 :=
  rfl

@[simp] theorem node2Counted_checks_eq_budget (previous : Node1Stage.{u}) :
    (node2Counted previous).checks = node2WorkBudget.checks previous :=
  rfl

/-- The Core binary decision satisfies its constant one-check work budget. -/
theorem node2_work_bounded (previous : Node1Stage.{u}) :
    (node2Counted previous).checks <=
      node2WorkBudget.coefficient *
        (node2WorkBudget.size previous + 1) ^ node2WorkBudget.degree := by
  rw [node2Counted_checks_eq_budget]
  exact node2WorkBudget.bounded previous

/-- Proof-relevant audit record for the node-2 counterexample decision. -/
def node2Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node1Stage.{u} Node1Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node2", "node2Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node2", "node2Decision.yesDecidable"⟩,
      .decisionProcedure⟩,
    ⟨⟨"HypostructureErdos64EG.Node2", "node2Decision.no_of_not_yes"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node1", "node1ResidualQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node1", "node1ResidualQuery"⟩
    Result := fun _stage => InitialResidual.{u}
    query := node1ResidualQuery
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Core.Residual.Decision", "Decision.Node.run"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Decision", "Decision.Binary"⟩,
      .typedOutcome⟩,
    ⟨⟨"Hypostructure.Core.Residual.Ledger", "Ledger.extend"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Residual.Decision", "Decision.Node.run_previous"⟩,
    ⟨"Hypostructure.Core.Budget.Work", "PolynomialCheckBudget.constant"⟩
  ]
  workBound := node2WorkBudget
  manualObligations := []

/-- Node 2 has no unrecorded mathematical or routing obligation. -/
def node2MetadataComplete :
    Core.Metadata.Complete node2Metadata :=
  ⟨rfl⟩

theorem node2_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node2Metadata.manualObligations) :=
  node2MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same one-check budget used by the counted run. -/
theorem node2_metadata_work_bounded (previous : Node1Stage.{u}) :
    node2Metadata.workBound.checks previous <=
      node2Metadata.workBound.coefficient *
        (node2Metadata.workBound.size previous + 1) ^
          node2Metadata.workBound.degree :=
  node2MetadataComplete.work_bounded previous

#print axioms node2
#print axioms node2_exhaustive
#print axioms node2_yes_branch_of_counterexample
#print axioms node2_no_branch_of_target
#print axioms node2Counted_checks_eq_one
#print axioms node2Counted_checks_eq_budget
#print axioms node2_work_bounded
#print axioms node2_metadata_has_no_manual_obligation
#print axioms node2_metadata_work_bounded

end HypostructureErdos64EG
