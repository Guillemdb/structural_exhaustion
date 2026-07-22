import Hypostructure.Graph.BoundariedAtom

/-!
# Proper boundaried-atom fixture

A complete three-vertex atom is glued to one isolated outside vertex.  The
fixture checks genuine properness, exact local observables, framework-owned
focused execution, and literal predecessor retention.
-/

namespace Hypostructure.Fixtures.GraphBoundariedAtom

open Hypostructure
open Hypostructure.Graph

/-- Two labelled boundary vertices. -/
def boundary : Boundary where
  Vertex := Fin 2
  vertices := inferInstance

/-- A triangle on the two boundary vertices and one internal vertex. -/
def piece : BoundaryPiece boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

/-- One isolated outside vertex. -/
def outside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

noncomputable def ambient : FiniteObject :=
  glue piece outside

noncomputable def decomposition : OwnedDecomposition ambient where
  interface := boundary
  piece := piece
  outside := outside
  vertexEquiv := Equiv.refl _
  ownsAdjacency := by
    intro left right
    change (glueGraph piece outside).Adj left right ↔
      OwnedAdjacency piece outside left right
    exact glueGraph_adj_iff piece outside left right

theorem piece_connected : piece.graph.Connected := by
  simp [piece]

theorem piece_vertexCount : piece.pack.vertexCount = 3 := by
  rfl

theorem ambient_vertexCount : ambient.vertexCount = 4 := by
  rw [ambient, glue_vertexCount]
  decide

theorem piece_edgeCount : piece.edgeCount = 3 := by
  decide

theorem piece_boundaryDegree (vertex : Fin 2) :
    piece.boundaryDegree vertex = 2 := by
  fin_cases vertex <;> decide

theorem piece_internalThreshold :
    piece.InternalThresholdBaseline 2 := by
  intro internal
  cases internal
  decide

noncomputable def atom : ProperBoundariedAtom ambient where
  decomposition := decomposition
  connected := piece_connected
  proper := by
    intro complete
    obtain ⟨source, sourceEq⟩ := complete.1 (.inr (.inr ()))
    rcases source with boundaryVertex | internalVertex
    · change Sum.inl boundaryVertex = Sum.inr (Sum.inr ()) at sourceEq
      cases sourceEq
    · change Sum.inr (Sum.inl internalVertex) =
        Sum.inr (Sum.inr ()) at sourceEq
      cases sourceEq

def Baseline (object : FiniteObject) : Prop :=
  object.lexicographicSize = ambient.lexicographicSize

def BranchState (_object : FiniteObject) := Unit

def Target (_object : FiniteObject) : Prop := False

noncomputable def context : Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState) where
  toAvoidingContext := {
    toBranchContext := {
      G := ambient
      baseline := rfl
      state := ()
    }
    avoids := id
  }
  minimal := by
    intro candidate smaller baseline
    rw [lexicographicProgress_smaller_iff,
      FiniteObject.LexicographicallySmaller, baseline] at smaller
    exact False.elim
      ((wellFounded_lt.prod_lex wellFounded_lt).irrefl.irrefl _ smaller)

/-- The literal predecessor carries its context as one accumulated entry. -/
abbrev Previous := Core.Residual.Ledger.Extension Unit (fun _ =>
  Core.MinimalCounterexampleContext
    (problem Baseline BranchState) Target
    (lexicographicProgress Baseline BranchState))

noncomputable def previous : Previous :=
  Core.Residual.Ledger.extend () context

abbrev focus : Core.Residual.Focus.Profile Previous :=
  Core.Residual.Focus.always Previous

def contextQuery : Core.Residual.Focus.ActiveQuery focus
    (fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.ActiveQuery.ofQuery Core.Residual.Query.latest

noncomputable def countedStage :=
  executeFocusedBoundariedAtomRegistrationCounted focus contextQuery previous

noncomputable def stage := countedStage.value

def active : focus.Active previous := True.intro

noncomputable def registration : BoundariedAtomRegistration context :=
  (focusedBoundariedAtomRegistrationQuery focus contextQuery).read stage active

noncomputable def executionCertificate :=
  (focusedBoundariedAtomCertificateQuery focus contextQuery).read stage active

noncomputable def certificate : BoundariedAtomProfileCertificate atom :=
  registration.family atom

theorem executor_retains_predecessor : stage.previous = previous :=
  rfl

theorem generated_profile_exact
    (vertex : atom.decomposition.interface.Vertex) :
    certificate.boundaryDegreeProfile vertex = 2 := by
  rw [certificate.profile_apply]
  change piece.boundaryDegree (show Fin 2 from vertex) = 2
  exact piece_boundaryDegree vertex

theorem generated_atom_is_proper :
    certificate.properSubgraph.value.LexicographicallySmaller ambient :=
  certificate.properSubgraph.decreases

theorem generated_profile_mismatch_rejected
    {otherBoundary : Boundary.{0}}
    {left right : BoundaryPiece otherBoundary}
    (different :
      left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) :
    ¬ BoundaryProfileTargetComplete Target left right :=
  registration.profileMismatchRejected different

theorem generated_checks_eq_zero : registration.checks = 0 :=
  registration.checks_eq_zero

/-- The public focus owns every predecessor, so the complete executor performs
no branch inspection in this fixture. -/
theorem executor_checks_eq_zero : executionCertificate.checks = 0 := by
  exact executionCertificate.checks_eq_budget

theorem counted_executor_checks_eq_zero : countedStage.checks = 0 := by
  change
    (executeFocusedBoundariedAtomRegistrationCounted
      focus contextQuery previous).checks = 0
  rw [executeFocusedBoundariedAtomRegistrationCounted_checks]
  rfl

/-- The certificate stored in the latest ledger entry reports the same work as
the counted execution that produced that entry. -/
theorem certificate_matches_counted_execution :
    executionCertificate.checks = countedStage.checks := by
  rw [executor_checks_eq_zero, counted_executor_checks_eq_zero]

theorem executor_work_bounded :
    executionCertificate.checks ≤
      focus.selectionBudget.coefficient *
        (focus.selectionBudget.size previous + 1) ^
          focus.selectionBudget.degree :=
  executionCertificate.work_bounded

theorem generated_work_bounded :
    registration.checks ≤
      boundariedAtomWorkBudget.coefficient *
        (boundariedAtomWorkBudget.size context.G + 1) ^
          boundariedAtomWorkBudget.degree :=
  registration.work_bounded

def metadata := focusedBoundariedAtomMetadata focus contextQuery

def metadataComplete : Core.Metadata.Complete metadata :=
  focusedBoundariedAtomMetadataComplete focus contextQuery

theorem metadata_records_active_query :
    metadata.focusedLedgerQueries.length = 1 :=
  rfl

theorem metadata_has_no_manual_obligation
    (obligation : Core.Metadata.ManualObligation) :
    ¬ obligation ∈ metadata.manualObligations :=
  metadataComplete.no_manual_obligation obligation

#print axioms executeFocusedBoundariedAtomRegistration
#print axioms focusedBoundariedAtomRegistrationQuery
#print axioms executor_retains_predecessor
#print axioms generated_profile_exact
#print axioms generated_atom_is_proper
#print axioms generated_profile_mismatch_rejected
#print axioms generated_checks_eq_zero
#print axioms executor_checks_eq_zero
#print axioms counted_executor_checks_eq_zero
#print axioms certificate_matches_counted_execution
#print axioms executor_work_bounded
#print axioms generated_work_bounded
#print axioms metadata_records_active_query
#print axioms metadata_has_no_manual_obligation

end Hypostructure.Fixtures.GraphBoundariedAtom
