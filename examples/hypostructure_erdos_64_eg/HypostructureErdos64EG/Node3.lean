import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Closure
import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.Focus
import HypostructureErdos64EG.Node2

/-!
# Diagram node 3: not-a-counterexample terminal

Node 3 is exactly the terminal on node 2's negative branch. It consumes
Core's proof that the literal node-2 decision selected that constructor and
returns the official theorem conclusion through Core's direct closure.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The official conclusion for the exact packed object in a node-1 stage. -/
abbrev Node3OfficialConclusion (stage : Node1Stage.{u}) : Prop :=
  let object := (node1ResidualQuery.read stage).object
  ∃ (exponent : Nat) (vertex : object.Vertex)
      (cycle : object.graph.Walk vertex vertex),
    exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent

/-- Read the proof from node 2's exact selected no constructor. -/
def node3TargetQuery :
    Core.Residual.Focus.ActiveQuery
      (Core.Residual.Focus.no
        (Yes := IsCounterexample) (No := IsNotCounterexample))
      (fun stage _active => IsNotCounterexample stage.previous) :=
  Core.Residual.Focus.noProof

/-- Node 2's selected no constructor entails the official theorem
conclusion for the unchanged root graph. -/
theorem node3_officialConclusion (previous : Node2Stage.{u})
    (active : (Core.Residual.Focus.no
      (Yes := IsCounterexample) (No := IsNotCounterexample)).Active previous) :
    Node3OfficialConclusion previous.previous :=
  (target_iff_official_conclusion
    (node1ResidualQuery.read previous.previous).object).mp
      (node3TargetQuery.read previous active)

/-- Node 3 terminates the exact node-2 no branch by direct certificate. -/
def node3 (previous : Node2Stage.{u})
    (active : (Core.Residual.Focus.no
      (Yes := IsCounterexample) (No := IsNotCounterexample)).Active previous) :
    Core.Closure.Result (Node3OfficialConclusion previous.previous) :=
  Core.Closure.Result.direct
    (.certificate (node3_officialConclusion previous active))

/-- Node 3 is a proof-only terminal, so it performs no primitive checks. -/
def node3WorkBudget :
    Core.PolynomialCheckBudget Node2Stage.{u} :=
  Core.PolynomialCheckBudget.proofOnly Node2Stage.{u}

/-- Node 3 uses Core's direct-certificate closure mechanism. -/
theorem node3_closure_mechanism (previous : Node2Stage.{u})
    (active : (Core.Residual.Focus.no
      (Yes := IsCounterexample) (No := IsNotCounterexample)).Active previous) :
    (node3 previous active).mechanism = Core.Closure.Mechanism.direct :=
  rfl

@[simp] theorem node3_checks_eq_zero (previous : Node2Stage.{u}) :
    node3WorkBudget.checks previous = 0 :=
  Core.PolynomialCheckBudget.proofOnly_checks _ _

/-- The proof-only terminal satisfies Core's zero-check polynomial budget. -/
theorem node3_work_bounded (previous : Node2Stage.{u}) :
    node3WorkBudget.checks previous ≤
      node3WorkBudget.coefficient *
        (node3WorkBudget.size previous + 1) ^ node3WorkBudget.degree :=
  node3WorkBudget.bounded previous

/-- Proof-relevant audit record for the node-3 direct terminal closure. -/
def node3Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, 0, u + 1}
      Node2Stage.{u} Node2Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node3", "node3"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.Node3", "node3_officialConclusion"⟩,
      .semanticLaw⟩
  ]
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node2", "node2"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node3", "node3TargetQuery"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.Core.Closure", "Closure.Result.direct"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Closure", "Closure.Result"⟩,
      .closureResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Closure", "Closure.Result.direct"⟩,
    ⟨"Hypostructure.Core.Budget.Work",
      "PolynomialCheckBudget.proofOnly_checks"⟩
  ]
  closureMechanisms := [Core.Closure.Mechanism.direct]
  workBound := node3WorkBudget
  manualObligations := []

/-- Node 3 has no unrecorded mathematical or routing obligation. -/
def node3MetadataComplete :
    Core.Metadata.Complete node3Metadata :=
  ⟨rfl⟩

theorem node3_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node3Metadata.manualObligations) :=
  node3MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same zero-work bound used by the terminal. -/
theorem node3_metadata_work_bounded (previous : Node2Stage.{u}) :
    node3Metadata.workBound.checks previous <=
      node3Metadata.workBound.coefficient *
        (node3Metadata.workBound.size previous + 1) ^
          node3Metadata.workBound.degree :=
  node3MetadataComplete.work_bounded previous

#print axioms node3
#print axioms node3_officialConclusion
#print axioms node3_closure_mechanism
#print axioms node3_checks_eq_zero
#print axioms node3_work_bounded
#print axioms node3_metadata_has_no_manual_obligation
#print axioms node3_metadata_work_bounded

end HypostructureErdos64EG
