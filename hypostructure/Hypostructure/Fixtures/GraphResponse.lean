import Hypostructure.Graph.Response

/-!
# Exact graph response fixtures

Two pieces share one labelled boundary and one internal vertex.  Their target
responses are compared only on the two outside contexts listed in the literal
residual schedule.  Core constructs the tables, proves finite neutrality,
selects the first distinction, and retains the incoming schedule ledger.
-/

namespace Hypostructure.Fixtures.GraphResponse

open Hypostructure.Core
open Hypostructure.Core.Response
open Hypostructure.Core.Response.FiniteTable
open Hypostructure.Graph

/-- One labelled boundary vertex. -/
def boundary : Boundary where
  Vertex := Unit
  vertices := inferInstance

/-- A piece containing its boundary--internal edge. -/
def edgePiece : BoundaryPiece boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance

/-- A same-interface piece with no edges. -/
def emptyPiece : BoundaryPiece boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by
    infer_instance

/-- A normalized outside context containing its boundary--internal edge. -/
def edgeOutside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊤
  decideAdj := by
    letI : DecidableEq boundary.Vertex := boundary.vertices.decEq
    infer_instance
  noBoundaryEdge := by
    intro left right
    cases left
    cases right
    simp

/-- A normalized outside context with no edges. -/
def emptyOutside : OutsideContext boundary where
  Internal := Unit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := by
    infer_instance
  noBoundaryEdge := by
    simp

/-- The residual-owned context codes are explicit; no graph space is scanned. -/
def outsideByCode : Bool -> OutsideContext boundary
  | false => edgeOutside
  | true => emptyOutside

/-- The exact order first checks the shared outside edge, then the empty
outside context. -/
def contextSchedule : ExactSchedule Bool :=
  ExactSchedule.ofList [false, true]

/-- Both semantic context codes are realized by the exact schedule. -/
theorem contextSchedule_complete (context : Bool) :
    Exists fun index : Fin contextSchedule.coordinates.length =>
      context = id (contextSchedule.coordinates.get index) := by
  cases context
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩

def representatives : Representatives (BoundaryPiece boundary) where
  source := edgePiece
  replacement := emptyPiece

/-- Isomorphism-invariant target used for the neutral response table. -/
def HasThreeVertices (object : FiniteObject) : Prop :=
  object.vertexCount = 3

def hasThreeVerticesDecidable (object : FiniteObject) :
    Decidable (HasThreeVertices object) := by
  unfold HasThreeVertices
  infer_instance

def hasThreeVerticesInterface : TargetInterface HasThreeVertices where
  isomorphismInvariant := {
    iff_of_iso := by
      intro left right equivalent
      constructor
      · intro leftHasThree
        rw [HasThreeVertices, ← left.vertexCount_eq_of_isomorphic equivalent]
        exact leftHasThree
      · intro rightHasThree
        rw [HasThreeVertices, left.vertexCount_eq_of_isomorphic equivalent]
        exact rightHasThree
  }

noncomputable def sizeResponses :=
  Graph.Response.targetSystem HasThreeVertices hasThreeVerticesDecidable
    Bool outsideByCode Bool id

noncomputable def sizeMeaning :=
  Graph.Response.targetSemantics HasThreeVertices hasThreeVerticesDecidable
    Bool outsideByCode Bool id

local instance sizeResponseDecidableEq : DecidableEq sizeResponses.Value := by
  change DecidableEq Bool
  infer_instance

theorem edgePiece_hasThreeVertices (context : Bool) :
    HasThreeVertices (glue edgePiece (outsideByCode context)) := by
  cases context <;>
    unfold HasThreeVertices <;>
    rw [glue_vertexCount] <;>
    decide

theorem emptyPiece_hasThreeVertices (context : Bool) :
    HasThreeVertices (glue emptyPiece (outsideByCode context)) := by
  cases context <;>
    unfold HasThreeVertices <;>
    rw [glue_vertexCount] <;>
    decide

theorem size_source_coordinate_true (coordinate : Bool) :
    sizeResponses.coordinateResponse representatives.source coordinate = true := by
  calc
    sizeResponses.coordinateResponse representatives.source coordinate =
        sizeResponses.contextResponse representatives.source
          (sizeResponses.decode coordinate) :=
      sizeResponses.coordinateExact representatives.source coordinate
    _ = true := by
      apply (sizeMeaning.target_iff_accepts representatives.source
        (sizeResponses.decode coordinate)).mp
      change HasThreeVertices (glue edgePiece (outsideByCode coordinate))
      exact edgePiece_hasThreeVertices coordinate

theorem size_replacement_coordinate_true (coordinate : Bool) :
    sizeResponses.coordinateResponse representatives.replacement coordinate = true := by
  calc
    sizeResponses.coordinateResponse representatives.replacement coordinate =
        sizeResponses.contextResponse representatives.replacement
          (sizeResponses.decode coordinate) :=
      sizeResponses.coordinateExact representatives.replacement coordinate
    _ = true := by
      apply (sizeMeaning.target_iff_accepts representatives.replacement
        (sizeResponses.decode coordinate)).mp
      change HasThreeVertices (glue emptyPiece (outsideByCode coordinate))
      exact emptyPiece_hasThreeVertices coordinate

/-- Core's exact table for the two same-boundary pieces. -/
noncomputable def equalTable :=
  Table.build sizeResponses representatives contextSchedule

theorem equalTable_not_distinguishing :
    Not (Distinguishes equalTable) := by
  rintro ⟨index, differs⟩
  apply differs
  have sourceTrue : equalTable.sourceVector index = (true : Bool) :=
    (equalTable.sourceExact index).trans (size_source_coordinate_true _)
  have replacementTrue :
      equalTable.replacementVector index = (true : Bool) :=
    (equalTable.replacementExact index).trans
      (size_replacement_coordinate_true _)
  exact sourceTrue.trans replacementTrue.symm

/-- Neutrality is produced by Core from absence of a finite distinction. -/
noncomputable def equalResponseTable : Neutrality equalTable :=
  equalTable.neutralityOfNotDistinguishes equalTable_not_distinguishing

/-- Exact context completeness is the only bridge from finite equality to
target-complete same-interface equivalence. -/
noncomputable def sizeTargetComplete :
    TargetCompleteEquivalence sizeMeaning representatives :=
  Graph.Response.targetCompleteOfExactContexts representatives contextSchedule
    equalResponseTable contextSchedule_complete

/-- Isomorphism-invariant target used for the distinguishing table. -/
def HasEdge (object : FiniteObject) : Prop :=
  Exists fun left => Exists fun right => object.graph.Adj left right

def hasEdgeDecidable (object : FiniteObject) : Decidable (HasEdge object) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold HasEdge
  infer_instance

def hasEdgeInterface : TargetInterface HasEdge where
  isomorphismInvariant := {
    iff_of_iso := by
      intro left right equivalent
      rcases equivalent with ⟨iso⟩
      constructor
      · rintro ⟨leftVertex, rightVertex, adjacent⟩
        exact ⟨iso leftVertex, iso rightVertex, map_rel iso adjacent⟩
      · rintro ⟨leftVertex, rightVertex, adjacent⟩
        exact ⟨iso.symm leftVertex, iso.symm rightVertex,
          map_rel iso.symm adjacent⟩
  }

theorem hasEdge_of_pieceAdj
    {piece : BoundaryPiece boundary} {outside : OutsideContext boundary}
    {left right : boundary.Vertex ⊕ piece.Internal}
    (adjacent : piece.graph.Adj left right) :
    HasEdge (glue piece outside) := by
  change Exists fun gluedLeft : GluedVertex piece outside =>
    Exists fun gluedRight : GluedVertex piece outside =>
      (glueGraph piece outside).Adj gluedLeft gluedRight
  refine ⟨pieceEmbedding piece outside left,
    pieceEmbedding piece outside right, ?_⟩
  rw [glueGraph_adj_iff]
  exact Or.inl ⟨left, right, adjacent, rfl, rfl⟩

theorem hasEdge_of_contextAdj
    {piece : BoundaryPiece boundary} {outside : OutsideContext boundary}
    {left right : boundary.Vertex ⊕ outside.Internal}
    (adjacent : outside.graph.Adj left right) :
    HasEdge (glue piece outside) := by
  change Exists fun gluedLeft : GluedVertex piece outside =>
    Exists fun gluedRight : GluedVertex piece outside =>
      (glueGraph piece outside).Adj gluedLeft gluedRight
  refine ⟨contextEmbedding piece outside left,
    contextEmbedding piece outside right, ?_⟩
  rw [glueGraph_adj_iff]
  exact Or.inr ⟨left, right, adjacent, rfl, rfl⟩

theorem edgePiece_hasEdge (context : Bool) :
    HasEdge (glue edgePiece (outsideByCode context)) := by
  apply hasEdge_of_pieceAdj
    (left := Sum.inl ()) (right := Sum.inr ())
  simp [edgePiece]

theorem emptyPiece_hasEdge_with_edgeOutside :
    HasEdge (glue emptyPiece edgeOutside) := by
  apply hasEdge_of_contextAdj
    (left := Sum.inl ()) (right := Sum.inr ())
  simp [edgeOutside]

theorem emptyPiece_hasNoEdge_with_emptyOutside :
    Not (HasEdge (glue emptyPiece emptyOutside)) := by
  change Not (Exists fun left : GluedVertex emptyPiece emptyOutside =>
    Exists fun right : GluedVertex emptyPiece emptyOutside =>
      (glueGraph emptyPiece emptyOutside).Adj left right)
  rintro ⟨left, right, adjacent⟩
  rw [glueGraph_adj_iff] at adjacent
  rcases adjacent with pieceOwned | contextOwned
  · rcases pieceOwned with ⟨pieceLeft, pieceRight, pieceAdjacent, _⟩
    simp [emptyPiece] at pieceAdjacent
  · rcases contextOwned with
      ⟨contextLeft, contextRight, contextAdjacent, _⟩
    simp [emptyOutside] at contextAdjacent

noncomputable def edgeResponses :=
  Graph.Response.targetSystem HasEdge hasEdgeDecidable
    Bool outsideByCode Bool id

noncomputable def edgeMeaning :=
  Graph.Response.targetSemantics HasEdge hasEdgeDecidable
    Bool outsideByCode Bool id

local instance edgeResponseDecidableEq : DecidableEq edgeResponses.Value := by
  change DecidableEq Bool
  infer_instance

theorem edge_context_response_true
    (piece : BoundaryPiece boundary) (context : Bool)
    (target : HasEdge (glue piece (outsideByCode context))) :
    edgeResponses.contextResponse piece context = true := by
  apply (edgeMeaning.target_iff_accepts piece context).mp
  exact target

theorem edge_context_response_false
    (piece : BoundaryPiece boundary) (context : Bool)
    (avoids : Not (HasEdge (glue piece (outsideByCode context)))) :
    edgeResponses.contextResponse piece context = false := by
  generalize responseEq : edgeResponses.contextResponse piece context = response
  cases response
  · rfl
  · exfalso
    apply avoids
    apply (edgeMeaning.target_iff_accepts piece context).mpr
    exact responseEq

theorem edge_coordinate_response_true
    (piece : BoundaryPiece boundary) (coordinate : Bool)
    (target : HasEdge (glue piece (outsideByCode coordinate))) :
    edgeResponses.coordinateResponse piece coordinate = true :=
  (edgeResponses.coordinateExact piece coordinate).trans
    (edge_context_response_true piece coordinate target)

theorem edge_coordinate_response_false
    (piece : BoundaryPiece boundary) (coordinate : Bool)
    (avoids : Not (HasEdge (glue piece (outsideByCode coordinate)))) :
    edgeResponses.coordinateResponse piece coordinate = false :=
  (edgeResponses.coordinateExact piece coordinate).trans
    (edge_context_response_false piece coordinate avoids)

noncomputable def distinguishingTable :=
  Table.build edgeResponses representatives contextSchedule

/-- The empty outside context distinguishes the two pieces. -/
theorem edgeResponses_distinguish : Distinguishes distinguishingTable := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  intro equal
  have sourceTrue :
      distinguishingTable.sourceVector ⟨1, by decide⟩ = true := by
    rw [distinguishingTable.sourceExact]
    apply edge_coordinate_response_true
    exact edgePiece_hasEdge true
  have replacementFalse :
      distinguishingTable.replacementVector ⟨1, by decide⟩ = false := by
    rw [distinguishingTable.replacementExact]
    apply edge_coordinate_response_false
    exact emptyPiece_hasNoEdge_with_emptyOutside
  rw [sourceTrue, replacementFalse] at equal
  contradiction

/-- Core selects the earliest differing scheduled outside context. -/
noncomputable def firstDistinguishingContext :
    FirstDistinction distinguishingTable :=
  distinguishingTable.firstDistinction edgeResponses_distinguish

theorem firstDistinguishingContext_index :
    firstDistinguishingContext.index.val = 1 := by
  have inBounds : firstDistinguishingContext.index.val < 2 :=
    firstDistinguishingContext.index.isLt
  have nonzero : Not (firstDistinguishingContext.index.val = 0) := by
    intro isZero
    have indexEq : firstDistinguishingContext.index = ⟨0, by decide⟩ :=
      Fin.ext isZero
    have differs := firstDistinguishingContext.differs
    rw [indexEq] at differs
    apply differs
    have sourceTrue :
        distinguishingTable.sourceVector ⟨0, by decide⟩ = (true : Bool) :=
      (distinguishingTable.sourceExact _).trans
        (edge_coordinate_response_true edgePiece false
          (edgePiece_hasEdge false))
    have replacementTrue :
        distinguishingTable.replacementVector ⟨0, by decide⟩ =
          (true : Bool) :=
      (distinguishingTable.replacementExact _).trans
        (edge_coordinate_response_true emptyPiece false
          emptyPiece_hasEdge_with_edgeOutside)
    exact sourceTrue.trans replacementTrue.symm
  omega

theorem firstDistinguishingContext_is_emptyOutside :
    outsideByCode
      (contextSchedule.coordinates.get firstDistinguishingContext.index) =
        emptyOutside := by
  have indexEq : firstDistinguishingContext.index = ⟨1, by decide⟩ :=
    Fin.ext firstDistinguishingContext_index
  rw [indexEq]
  rfl

/-- The exact schedule is stored in, and read from, the literal predecessor
ledger used by Core classification. -/
abbrev ScheduleLedger := Residual.Ledger (ExactSchedule Bool)

def scheduleLedger : ScheduleLedger :=
  Residual.Ledger.initial contextSchedule

def scheduleQuery : Residual.Query ScheduleLedger
    (fun _previous => ExactSchedule edgeResponses.Coordinate) :=
  Residual.Query.residual

noncomputable def edgeClassification :=
  FiniteTable.run edgeResponses representatives scheduleQuery scheduleLedger

theorem classification_retains_schedule :
    edgeClassification.previous = scheduleLedger :=
  Residual.Decision.Node.run_previous
    (FiniteTable.classificationNode edgeResponses representatives scheduleQuery)
    scheduleLedger

#print axioms equalResponseTable
#print axioms sizeTargetComplete
#print axioms firstDistinguishingContext_index
#print axioms firstDistinguishingContext_is_emptyOutside
#print axioms classification_retains_schedule
#print axioms Graph.Response.extractedTarget_iff_accepts
#print axioms Graph.Response.exchangeAfterStrictOfCoverage

end Hypostructure.Fixtures.GraphResponse
