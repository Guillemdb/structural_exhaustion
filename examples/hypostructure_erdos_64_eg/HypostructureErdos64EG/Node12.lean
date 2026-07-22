import Hypostructure.Core.Metadata
import Hypostructure.Core.Residual.ProofProjection
import Hypostructure.Graph.Replacement
import HypostructureErdos64EG.Node11

/-!
# Diagram node 12: context universality

This node records the definitional projection from target completeness to
equal target response in every compatible outside context.  Core extends only
the active node-11 branch; inactive sibling branches remain in the literal
predecessor ledger.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- Minimal context inherited through node 11 by a framework query. -/
def node4ContextAtNode11Query :
    Core.Residual.Focus.ActiveQuery Node11Focus.{u}
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode10Query.{u}.preserve

/-- The original node-12 claim over one registered proper atom, any collection
of local response coordinates, and any certified target-complete quotient of
that collection. -/
abbrev Node12Claim :=
  Graph.FocusedRegisteredContextUniversalityClaim.{u, 0, v, u + 1}
    (focus := Node11Focus.{u}) (Baseline := Baseline)
    (BranchState := BranchState) (Target := Target)
    node4ContextAtNode11Query node11RegistrationQuery.{u}

/-- Derive the paper's definitional implication from Node 11's exact latest
registration query.  The registration value is read, never copied. -/
def node12ProjectionQuery :
    Core.Residual.Focus.ActiveQuery Node11Focus.{u} Node12Claim.{u, v} :=
  Graph.focusedRegisteredContextUniversalityProjectionQuery.{u, 0, u + 1, v}
    (focus := Node11Focus.{u}) (Baseline := Baseline)
    (BranchState := BranchState) (Target := Target)
    node4ContextAtNode11Query node11RegistrationQuery.{u}

/-- Exact accumulated stage emitted by Core's proof-projection executor. -/
abbrev Node12Stage :=
  Core.Residual.ProofProjection.Stage Node11Focus.{u} Node12Claim.{u, v}

/-- Counted node-12 execution, including the inactive outcome. -/
def node12Counted (previous : Node11Stage.{u}) :
    Core.Counted Node12Stage.{u, v} :=
  Core.Residual.ProofProjection.executeCounted Node11Focus.{u}
    Node12Claim.{u, v} node12ProjectionQuery previous

/-- Apply Graph's target-completeness projection on the literal node-11
stage.  Core owns active-branch routing and ledger extension. -/
def node12 (previous : Node11Stage.{u}) : Node12Stage.{u, v} :=
  (node12Counted previous).value

/-- Focus inherited by the replacement node. -/
abbrev Node12Focus :=
  Core.Residual.ProofProjection.Profile Node11Focus.{u} Node12Claim.{u, v}

/-- Query the private Core certificate introduced by node 12. -/
def node12CertificateQuery :=
  Core.Residual.ProofProjection.latest Node11Focus.{u} Node12Claim.{u, v}

/-- Query the context-universality fact from the newest ledger entry. -/
def node12ContextUniversalityQuery :
    Core.Residual.Focus.ActiveQuery Node12Focus.{u, v}
      (fun stage active => Node12Claim.{u, v} stage.previous active) :=
  Core.Residual.ProofProjection.latestClaim Node11Focus.{u}
    Node12Claim.{u, v}

/-- Canonical work budget for the node-12 proof projection. -/
abbrev node12WorkBudget :=
  Core.Residual.ProofProjection.workBudget Node11Focus.{u}

@[simp] theorem node12_previous (previous : Node11Stage.{u}) :
    (node12 previous).previous = previous :=
  rfl

/-- Any two coordinates identified by any target-complete quotient of a
registered atom have identical target response against every literal outside
context. -/
theorem node12_context_universal (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode11Query.read stage.previous active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, v}
      ((node11RegistrationQuery.{u}.read stage.previous active).family atom) Target)
    (quotient : Graph.AtomResponse.TargetCompleteQuotient.{u, v} system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  node12ContextUniversalityQuery.read stage active atom system quotient identified

/-- Every local coordinate is attached to Node 11's exact registered boundary
profile rather than to an application-copied profile. -/
theorem node12_coordinate_profile_registered (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode11Query.read stage.previous active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, v}
      ((node11RegistrationQuery.{u}.read stage.previous active).family atom) Target)
    (coordinate : system.Coordinate) :
    system.boundaryDegreeProfile coordinate =
      Graph.BoundariedAtomProfileCertificate.boundaryDegreeProfile
        ((node11RegistrationQuery.{u}.read stage.previous active).family atom) :=
  system.in_registered_fibre coordinate

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node12Counted_checks_eq_one
    (previous : Node11Stage.{u}) :
    (node12Counted.{u, v} previous).checks = 1 := by
  rw [node12Counted,
    Core.Residual.ProofProjection.executeCounted_checks]
  rfl

theorem node12Counted_work_bounded (previous : Node11Stage.{u}) :
    node12WorkBudget.Within previous
      (node12Counted.{u, v} previous).checks :=
  by
    rw [node12Counted]
    exact Core.Residual.ProofProjection.executeCounted_work_within
      Node11Focus.{u} Node12Claim.{u, v} node12ProjectionQuery previous

@[simp] theorem node12_checks_eq_one (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage) :
    (node12CertificateQuery.read stage active).checks = 1 := by
  exact (node12CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The single counted focus selection satisfies its Core-owned polynomial
envelope; deriving the context-universality implication adds no local check. -/
theorem node12_work_bounded (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage) :
    node12WorkBudget.Within stage.previous
      (node12CertificateQuery.read stage active).checks :=
  (node12CertificateQuery.read stage active).work_within

/-- Proof-relevant audit record for node-12 context-universality projection. -/
noncomputable def node12Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, max (u + 1) (v + 1), u + 1}
      Node11Stage.{u} Node11Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node12", "node12Counted"⟩
  primitiveInputs := []
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node11", "node11"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node11",
      "node11RegistrationQuery.{u}"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node12",
      "node12ProjectionQuery"⟩,
      .registeredProfile⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := []
  frameworkSearch := [
    ⟨"Hypostructure.Core.Residual.ProofProjection",
      "executeCounted"⟩,
    ⟨"Hypostructure.Graph.AtomResponse",
      "TargetCompleteQuotient.contextUniversal_of_identified"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Certificate"⟩, .auditRecord⟩,
    ⟨⟨"Hypostructure.Core.Residual.ProofProjection",
      "Stage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.AtomResponse",
      "TargetCompleteQuotient.contextUniversal_of_identified"⟩,
    ⟨"Hypostructure.Graph.AtomResponse",
      "CoordinateSystem.in_registered_fibre"⟩,
    ⟨"Hypostructure.Core.Residual.ProofProjection",
      "executeCounted_work_within"⟩
  ]
  closureMechanisms := []
  workBound := node12WorkBudget
  manualObligations := []

/-- Node 12 has no unrecorded mathematical or routing obligation. -/
def node12MetadataComplete :
    Core.Metadata.Complete node12Metadata :=
  ⟨rfl⟩

theorem node12_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node12Metadata.manualObligations) :=
  node12MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused proof-projection work bound used by
the executor. -/
theorem node12_metadata_work_bounded (previous : Node11Stage.{u}) :
    node12Metadata.workBound.Within previous
      (node12Metadata.workBound.checks previous) :=
  node12MetadataComplete.work_within previous

#print axioms node12
#print axioms node12_context_universal
#print axioms node12_coordinate_profile_registered
#print axioms node12Counted_checks_eq_one
#print axioms node12Counted_work_bounded
#print axioms node12_checks_eq_one
#print axioms node12_work_bounded
#print axioms node12_metadata_has_no_manual_obligation
#print axioms node12_metadata_work_bounded

end HypostructureErdos64EG
