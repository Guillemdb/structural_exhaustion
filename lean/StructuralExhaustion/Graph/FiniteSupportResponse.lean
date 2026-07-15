import StructuralExhaustion.CT15.AdmissibleQuotient
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Graph.FiniteSupportResponse

open StructuralExhaustion

universe u v

/-!
# Exact responses of finitely supported graph coordinates

All coordinates share the ambient vertex labels as a common boundary type.
For one coordinate, the piece is the literal induced graph on its declared
finite support, embedded into those labels with no anonymous internal
vertices.  Its boundary value is the exact degree function, and its response
to an outside context is the actual graph target after literal gluing.

The CT15 runner enumerates only the supplied coordinate schedule.  Outside
contexts occur under a universal proposition and are never materialized.
-/

variable {V : Type u}

/-- Embed a supported ambient vertex as a labelled boundary vertex. -/
def supportEmbedding (support : Finset V) :
    {vertex : V // vertex ∈ support} ↪ (V ⊕ PEmpty.{u + 1}) where
  toFun := fun vertex ↦ .inl vertex.1
  inj' := by
    intro left right equal
    exact Subtype.ext (Sum.inl.inj equal)

/-- Literal boundaried piece carried by one finite support. -/
noncomputable def piece (object : FiniteObject V) (support : Finset V) :
    PackedBoundariedGluing.Piece V where
  Internal := PEmpty.{u + 1}
  internalVertices := inferInstance
  graph := (object.induceFinset support).graph.map (supportEmbedding support)
  decideAdj := Classical.decRel _

/-- One finite coordinate family and the exact support attached to each
coordinate. -/
structure Profile
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (Coordinate : Type v) where
  coordinates : FinEnum Coordinate
  support : Coordinate → Finset ctx.G.Vertex

namespace Profile

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {Coordinate : Type v}
variable (profile : Profile input ctx Coordinate)

noncomputable def coordinatePiece (coordinate : Coordinate) :
    PackedBoundariedGluing.Piece ctx.G.Vertex :=
  piece ctx.G.object (profile.support coordinate)

/-- Exact target-response system for the supplied finite supports. -/
noncomputable def responseSystem :
    CT15.AdmissibleQuotient.ResponseSystem where
  Coordinate := Coordinate
  BoundaryValue := ctx.G.Vertex → Nat
  Context := PackedBoundariedGluing.Context ctx.G.Vertex
  boundary := fun coordinate ↦
    PackedBoundariedGluing.Piece.boundaryDegree
      ctx.G.object.input.vertices (profile.coordinatePiece coordinate)
  response := fun coordinate outside ↦
    @decide
      (input.Target
        (PackedBoundariedGluing.glue ctx.G.object.input.vertices
          (profile.coordinatePiece coordinate) outside))
      (Classical.propDecidable _)

@[simp] theorem response_true_iff (coordinate : Coordinate)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    profile.responseSystem.response coordinate outside = true ↔
      input.Target
        (PackedBoundariedGluing.glue ctx.G.object.input.vertices
          (profile.coordinatePiece coordinate) outside) := by
  simp [responseSystem]

/-- Reusable CT15 instantiation.  Admissible quotient failures are discharged
by the generic certified-reduction contract, so the graph application supplies
only coordinates and their exact finite supports. -/
noncomputable def ct15Profile : CT15.AdmissibleQuotient.Profile ctx where
  system := profile.responseSystem
  coordinates := profile.coordinates

noncomputable def run := profile.ct15Profile.run

theorem terminal : profile.run.terminal = .fullRankLedger :=
  profile.ct15Profile.terminal

theorem trace : profile.run.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] :=
  profile.ct15Profile.trace

theorem verified : profile.run.outcome.Valid :=
  profile.ct15Profile.verified

theorem total :
    ∃ result, result = profile.run ∧ result.outcome.Valid ∧
      @CT15.Graph.ValidTrace input.problem
        profile.ct15Profile.spec profile.ct15Profile.capability
        profile.ct15Profile.branchInput result.trace :=
  profile.ct15Profile.total

theorem linearWork :
    profile.ct15Profile.budget.checks () ≤
      profile.ct15Profile.budget.coefficient *
        (profile.ct15Profile.budget.size () + 1) ^
          profile.ct15Profile.budget.degree :=
  profile.ct15Profile.linearWork

end Profile

end StructuralExhaustion.Graph.FiniteSupportResponse
