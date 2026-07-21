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

/-- One isolated outside vertex; the context owns no boundary edge. -/
def outside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance
  noBoundaryEdge := by simp

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
  decreases :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
      change piece.pack.vertexCount < ambient.vertexCount
      rw [piece_vertexCount, ambient_vertexCount]
      decide)

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

def focus : Core.Residual.Focus.Profile Previous where
  Active := fun _previous => True
  activeDecidable := fun _previous => inferInstance

def contextQuery : Core.Residual.Focus.ActiveQuery focus
    (fun _previous _active =>
      Core.MinimalCounterexampleContext
        (problem Baseline BranchState) Target
        (lexicographicProgress Baseline BranchState)) :=
  Core.Residual.Focus.ActiveQuery.ofQuery Core.Residual.Query.latest

noncomputable def stage :=
  executeFocusedBoundariedAtomFamily focus contextQuery previous

def active : focus.Active previous := True.intro

noncomputable def certificate : BoundariedAtomProfileCertificate atom :=
  (focusedBoundariedAtomFamilyQuery focus contextQuery).read stage active atom

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

#print axioms executeFocusedBoundariedAtomFamily
#print axioms focusedBoundariedAtomFamilyQuery
#print axioms executor_retains_predecessor
#print axioms generated_profile_exact
#print axioms generated_atom_is_proper

end Hypostructure.Fixtures.GraphBoundariedAtom
