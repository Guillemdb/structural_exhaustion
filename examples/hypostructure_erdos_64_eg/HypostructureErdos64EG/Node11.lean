import Hypostructure.Core.Metadata
import Hypostructure.Graph.BoundariedAtom
import HypostructureErdos64EG.Node10

/-!
# Diagram node 11: proper boundaried atoms and degree profiles

Graph registers the universal family of proper connected atom occurrences in
the live minimal graph and derives each atom's uncapped boundary-degree
profile.  The application supplies no profile, successor payload, or route.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The minimal context inherited through node 10 by a framework query. -/
def node4ContextAtNode10Query :
    Core.Residual.Focus.ActiveQuery Node10Focus
      (fun _stage _active =>
        Core.MinimalCounterexampleContext problem Target EGProgress) :=
  node4ContextAtNode9Query.preserve

/-- Exact accumulated stage emitted by Graph's boundaried-atom executor. -/
abbrev Node11Stage :=
  Graph.FocusedBoundariedAtomStage Node10Focus node4ContextAtNode10Query

/-- Counted node-11 execution, including the inactive outcome. -/
noncomputable def node11Counted (previous : Node10Stage.{u}) :=
  Graph.executeFocusedBoundariedAtomRegistrationCounted Node10Focus
    node4ContextAtNode10Query previous

/-- Execute node 11 from the literal node-10 predecessor. -/
noncomputable def node11 (previous : Node10Stage.{u}) : Node11Stage.{u} :=
  (node11Counted previous).value

/-- Focus inherited by node 12. -/
abbrev Node11Focus :=
  Graph.FocusedBoundariedAtomProfile Node10Focus node4ContextAtNode10Query

/-- Query Graph's complete generated boundaried-atom registration. -/
def node11RegistrationQuery :=
  Graph.focusedBoundariedAtomRegistrationQuery Node10Focus
    node4ContextAtNode10Query

/-- Query Graph's private execution certificate and exact selector work. -/
def node11CertificateQuery :=
  Graph.focusedBoundariedAtomCertificateQuery Node10Focus
    node4ContextAtNode10Query

@[simp] theorem node11_previous (previous : Node10Stage.{u}) :
    (node11 previous).previous = previous :=
  rfl

/-- Every registered profile coordinate is Graph's uncapped local degree. -/
theorem node11_boundaryDegreeProfile (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous active).G)
    (vertex : atom.decomposition.interface.Vertex) :
    ((node11RegistrationQuery.read stage active).family atom).boundaryDegreeProfile
        vertex =
      atom.decomposition.piece.boundaryDegree vertex :=
  ((node11RegistrationQuery.read stage active).family atom).profile_apply vertex

/-- Pieces in different uncapped boundary-degree fibres cannot be identified
by the target-complete relation used downstream. -/
theorem node11_profileMismatchRejected (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage)
    {boundary : Graph.Boundary.{u}}
    {left right : Graph.BoundaryPiece boundary}
    (different : left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) :
    ¬ Graph.BoundaryProfileTargetComplete Target left right :=
  (node11RegistrationQuery.read stage active).profileMismatchRejected different

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node11Counted_checks_eq_one (previous : Node10Stage.{u}) :
    (node11Counted previous).checks = 1 := by
  change
    (Graph.executeFocusedBoundariedAtomRegistrationCounted Node10Focus
      node4ContextAtNode10Query previous).checks = 1
  rw [Graph.executeFocusedBoundariedAtomRegistrationCounted_checks]
  rfl

theorem node11Counted_work_bounded (previous : Node10Stage.{u}) :
    (node11Counted previous).checks ≤
      Node10Focus.selectionBudget.coefficient *
        (Node10Focus.selectionBudget.size previous + 1) ^
          Node10Focus.selectionBudget.degree :=
  Graph.executeFocusedBoundariedAtomRegistrationCounted_checks_bounded
    Node10Focus node4ContextAtNode10Query previous

/-- Node 11 performs one structural focus selection; deriving the atom family
and profiles adds no finite inspection. -/
theorem node11_checks_eq_one (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage) :
    (node11CertificateQuery.read stage active).checks = 1 := by
  exact (node11CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The registered work count satisfies Graph's uniform polynomial budget. -/
theorem node11_work_bounded (stage : Node11Stage.{u})
    (active : Node11Focus.Active stage) :
    (node11CertificateQuery.read stage active).checks ≤
      Node10Focus.selectionBudget.coefficient *
        (Node10Focus.selectionBudget.size stage.previous + 1) ^
          Node10Focus.selectionBudget.degree :=
  (node11CertificateQuery.read stage active).work_bounded

/-- Proof-relevant audit record for node-11 boundaried-atom registration. -/
noncomputable def node11Metadata :
    Core.Metadata.DeclarationMetadata.{u + 1, u + 1, u + 1}
      Node10Stage.{u} Node10Stage.{u} where
  declaration :=
    ⟨"HypostructureErdos64EG.Node11", "node11Counted"⟩
  primitiveInputs := []
  inferredDependencies := [
    ⟨⟨"HypostructureErdos64EG.Node10", "node10"⟩,
      .predecessorProjection⟩,
    ⟨⟨"HypostructureErdos64EG.Node11",
      "node4ContextAtNode10Query"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := []
  focusedLedgerQueries := [{
    source := ⟨"HypostructureErdos64EG.Node11",
      "node4ContextAtNode10Query"⟩
    profile := Node10Focus
    Result := fun _stage _active =>
      Core.MinimalCounterexampleContext problem Target EGProgress
    query := node4ContextAtNode10Query
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "executeFocusedBoundariedAtomRegistrationCounted"⟩,
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "deriveBoundariedAtomRegistration"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "BoundariedAtomRegistration"⟩, .typedOutcome⟩,
    ⟨⟨"Hypostructure.Graph.BoundariedAtom",
      "FocusedBoundariedAtomStage"⟩, .residualStage⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "BoundariedAtomProfileCertificate.profile_apply"⟩,
    ⟨"Hypostructure.Graph.Response",
      "profile_ne_not_targetComplete"⟩,
    ⟨"Hypostructure.Graph.BoundariedAtom",
      "executeFocusedBoundariedAtomRegistrationCounted_checks_bounded"⟩
  ]
  closureMechanisms := []
  workBound := Node10Focus.selectionBudget
  manualObligations := []

/-- Node 11 has no unrecorded mathematical or routing obligation. -/
def node11MetadataComplete :
    Core.Metadata.Complete node11Metadata :=
  ⟨rfl⟩

theorem node11_metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    Not (obligation ∈ node11Metadata.manualObligations) :=
  node11MetadataComplete.no_manual_obligation obligation

/-- The metadata stores the same focused-selection work bound used by the
executor. -/
theorem node11_metadata_work_bounded (previous : Node10Stage.{u}) :
    node11Metadata.workBound.checks previous <=
      node11Metadata.workBound.coefficient *
        (node11Metadata.workBound.size previous + 1) ^
          node11Metadata.workBound.degree :=
  node11MetadataComplete.work_bounded previous

#print axioms node11
#print axioms node11_boundaryDegreeProfile
#print axioms node11_profileMismatchRejected
#print axioms node11Counted_checks_eq_one
#print axioms node11Counted_work_bounded
#print axioms node11_checks_eq_one
#print axioms node11_work_bounded
#print axioms node11_metadata_has_no_manual_obligation
#print axioms node11_metadata_work_bounded

end HypostructureErdos64EG
