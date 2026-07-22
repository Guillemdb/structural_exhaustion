import Hypostructure.Core.Metadata
import HypostructureErdos64EG.InitialResidual

/-!
# Diagram node 1: theorem-root graph

Node 1 is the sole application root.  It adds no mathematical premise and is
the only EG node allowed to initialize a residual ledger.
-/

namespace HypostructureErdos64EG

universe u

/-- Exact framework stage at diagram node 1. -/
abbrev Node1Stage := InitialStage.{u}

/-- Node 1 only installs theorem inputs, so it performs no primitive checks. -/
def node1WorkBudget :
    Hypostructure.Core.PolynomialCheckBudget InitialResidual.{u} :=
  Hypostructure.Core.PolynomialCheckBudget.proofOnly InitialResidual.{u}

/-- Counted root initialization. Installing the literal theorem input performs
no primitive inspection. -/
def node1Counted (residual : InitialResidual.{u}) :
    Hypostructure.Core.Counted Node1Stage.{u} :=
  Hypostructure.Core.Counted.pure (initialStage residual)

/-- Seed node 1 from the official graph and minimum-degree hypothesis. -/
def node1 (residual : InitialResidual.{u}) : Node1Stage.{u} :=
  (node1Counted residual).value

@[simp] theorem node1Counted_value (residual : InitialResidual.{u}) :
    (node1Counted residual).value = node1 residual :=
  rfl

@[simp] theorem node1_residual (residual : InitialResidual.{u}) :
    Hypostructure.Core.Residual.residualOf (node1 residual) = residual :=
  rfl

@[simp] theorem node1Counted_checks_eq_zero
    (residual : InitialResidual.{u}) :
    (node1Counted residual).checks = 0 :=
  rfl

/-- The counted initializer reports exactly its registered framework budget. -/
@[simp] theorem node1Counted_checks_eq_budget
    (residual : InitialResidual.{u}) :
    (node1Counted residual).checks = node1WorkBudget.checks residual :=
  rfl

/-- Root initialization satisfies Core's proof-only polynomial work budget. -/
theorem node1_work_bounded (residual : InitialResidual.{u}) :
    node1WorkBudget.Within residual (node1Counted residual).checks := by
  rw [node1Counted_checks_eq_budget]
  exact node1WorkBudget.checks_within residual

/-- Proof-relevant audit record for the unique EG root initializer. -/
def node1Metadata :
    Hypostructure.Core.Metadata.DeclarationMetadata.{u + 1, 0, u + 1}
      InitialResidual.{u} InitialResidual.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node1", "node1Counted"⟩
  primitiveInputs := [
    ⟨⟨"HypostructureErdos64EG.InitialResidual", "InitialResidual.object"⟩,
      .definition⟩,
    ⟨⟨"HypostructureErdos64EG.InitialResidual", "InitialResidual.baseline"⟩,
      .localCertificate⟩
  ]
  inferredDependencies := []
  ledgerQueries := []
  frameworkSearch := []
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.Ledger", "Ledger.initial"⟩,
      .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Residual.Ledger", "Ledger.residualOf_initial"⟩,
    ⟨"Hypostructure.Core.Budget.Work",
      "PolynomialCheckBudget.proofOnly_checks"⟩
  ]
  workBound := node1WorkBudget
  manualObligations := []

/-- Node 1 has no unrecorded mathematical or routing obligation. -/
def node1MetadataComplete :
    Hypostructure.Core.Metadata.Complete node1Metadata :=
  ⟨rfl⟩

theorem node1_metadata_has_no_manual_obligation
    (obligation : Hypostructure.Core.Metadata.ManualObligation) :
    Not (obligation ∈ node1Metadata.manualObligations) :=
  node1MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same zero-work bound used by the counted root. -/
theorem node1_metadata_work_bounded (residual : InitialResidual.{u}) :
    node1Metadata.workBound.Within residual
      (node1Metadata.workBound.checks residual) :=
  node1MetadataComplete.work_within residual

#print axioms node1
#print axioms node1_residual
#print axioms node1Counted_checks_eq_zero
#print axioms node1Counted_checks_eq_budget
#print axioms node1_work_bounded
#print axioms node1_metadata_has_no_manual_obligation
#print axioms node1_metadata_work_bounded

end HypostructureErdos64EG
