import Erdos64EG.P13SelectedWindowGermScale
import StructuralExhaustion.CT3.Automation
import StructuralExhaustion.Graph.Path

namespace Erdos64EG.Internal.P13ShortPathCT3

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor
open StructuralExhaustion.Graph.InducedPathColdGermScale
open P13SelectedWindowGermScale

universe u

variable (ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u})
variable (stub : CubicStub ctx.G.object)

noncomputable abbrev sourceLength : Nat :=
  (p13SelectedWindowCorridorProducer ctx).ambientReturn stub |>.length

/-- Canonical shorter path lengths.  This is a linear universe, rather than
all vertex words or boundaried ambient subgraphs. -/
abbrev Candidate :=
  {length : Fin (supportLength ctx stub) //
    0 < length.1 ∧ length.1 < sourceLength ctx stub}

@[implicit_reducible]
noncomputable def candidates : FinEnum (Candidate ctx stub) :=
  Core.Enumeration.subtype
    (inferInstance : FinEnum (Fin (supportLength ctx stub)))
    (fun length => 0 < length.1 ∧ length.1 < sourceLength ctx stub)
    (fun _ => inferInstance)

/-- Every coordinate is a possible simple return length in the finite ambient
graph, with zero retained as a harmless strengthening of the comparison. -/
abbrev Coordinate := Fin (ctx.G.object.input.vertices.card + 1)

@[implicit_reducible]
noncomputable def coordinates : FinEnum (Coordinate ctx) := inferInstance

def response (pieceLength : Nat) (returnLength : Coordinate ctx) : Bool :=
  decide (PowerOfTwoLength (pieceLength + returnLength.1))

theorem response_reflects_cycleLength
    (pieceLength : Nat) (returnLength : Coordinate ctx) :
    response ctx pieceLength returnLength = true ↔
      PowerOfTwoLength (pieceLength + returnLength.1) := by
  simp [response]

/-- Every actual simple return path has a coordinate in the declared finite
universe. -/
noncomputable def coordinateOfReturn
    {left right : ctx.G.Vertex} (walk : ctx.G.object.graph.Walk left right)
  (isPath : walk.IsPath) : Coordinate ctx := by
  refine ⟨walk.length, ?_⟩
  have supportBound : walk.support.length ≤
      ctx.G.object.input.vertices.card := by
    simpa only [FinEnum.orderedValues_length] using
      Core.Enumeration.length_le_elems_of_nodup
        ctx.G.object.input.vertices isPath.support_nodup
  rw [walk.length_support] at supportBound
  omega

theorem response_reflects_actualReturn
    (pieceLength : Nat) {left right : ctx.G.Vertex}
    (walk : ctx.G.object.graph.Walk left right) (isPath : walk.IsPath) :
    response ctx pieceLength (coordinateOfReturn ctx walk isPath) = true ↔
      PowerOfTwoLength (pieceLength + walk.length) := by
  exact response_reflects_cycleLength ctx pieceLength
    (coordinateOfReturn ctx walk isPath)

/-- Exact local CT3 specification.  Rows are the same canonical shorter
paths as candidates, and their stored bits are definitionally exact. -/
noncomputable abbrev spec : CT3.Spec PackedProblem.{u} where
  Piece := Nat
  Context := Coordinate ctx
  Candidate := Candidate ctx stub
  Row := Candidate ctx stub
  response := response ctx
  candidatePiece := fun candidate => candidate.1.1
  Admissible := fun _object _source _candidate => True
  Smaller := fun _object _source _candidate => True
  rowPiece := fun row => row.1.1
  rowResponse := fun row => response ctx row.1.1

private theorem candidateCard_le_vertices :
    (candidates ctx stub).card ≤ ctx.G.object.input.vertices.card := by
  calc
    (candidates ctx stub).card ≤ supportLength ctx stub := by
      simpa [FinEnum.card_eq_fintypeCard] using
        Core.Enumeration.subtype_card_le
          (inferInstance : FinEnum (Fin (supportLength ctx stub)))
          (fun length => 0 < length.1 ∧ length.1 < sourceLength ctx stub)
          (fun _ => inferInstance)
    _ ≤ ctx.G.object.input.vertices.card := by
      simpa only [FinEnum.orderedValues_length] using
        Core.Enumeration.length_le_elems_of_nodup
          ctx.G.object.input.vertices
          ((p13SelectedWindowCorridorProducer ctx).ambientReturn_isPath stub
            |>.support_nodup)

private theorem workBound :
    CT3.localCheckBound (coordinates ctx) (candidates ctx stub)
      (candidates ctx stub) ≤
        8 * (ctx.G.object.input.vertices.card + 1) ^ 2 := by
  have candidateBound := candidateCard_le_vertices ctx stub
  simp only [CT3.localCheckBound, FinEnum.orderedValues_length]
  simp only [FinEnum.card_eq_fintypeCard, Fintype.card_fin] at *
  nlinarith

noncomputable def capability : CT3.Capability (spec ctx stub) where
  contexts := coordinates ctx
  candidates := candidates ctx stub
  rows := candidates ctx stub
  admissibleDecidable := fun _object _source _candidate => .isTrue trivial
  smallerDecidable := fun _object _source _candidate => .isTrue trivial
  inputSize := fun _object => ctx.G.object.input.vertices.card
  workCoefficient := 8
  workDegree := 2
  workBound := by
    intro object
    simpa using workBound ctx stub

noncomputable def input : CT3.Input (spec ctx stub) where
  context := ctx.toBranchContext
  piece := sourceLength ctx stub

noncomputable def run :=
  CT3.run (spec ctx stub) (capability ctx stub) (input ctx stub)

/-- A CT3-matched candidate is a concrete canonical two-terminal path graph,
with positive length, strict length decrease, and exact response equality on
every declared return-length coordinate. -/
structure CertifiedReplacement (candidate : Candidate ctx stub) : Prop where
  positive : 0 < candidate.1.1
  shorter : candidate.1.1 < sourceLength ctx stub
  sameResponse : CT3.SameResponse (spec ctx stub)
    candidate.1.1 (sourceLength ctx stub)

/-- The concrete canonical graph realizing a certified replacement length. -/
abbrev CertifiedReplacement.graph {candidate : Candidate ctx stub}
    (_certificate : CertifiedReplacement ctx stub candidate) :=
  SimpleGraph.pathGraph (candidate.1.1 + 1)

theorem CertifiedReplacement.graph_connected
    {candidate : Candidate ctx stub}
    (_certificate : CertifiedReplacement ctx stub candidate) :
    (SimpleGraph.pathGraph (candidate.1.1 + 1)).Connected := by
  simpa using SimpleGraph.pathGraph_connected candidate.1.1

theorem CertifiedReplacement.endpoints_distinct
    {candidate : Candidate ctx stub}
    (_certificate : CertifiedReplacement ctx stub candidate) :
    (⟨0, by omega⟩ : Fin (candidate.1.1 + 1)) ≠
      ⟨candidate.1.1, by omega⟩ := by
  intro equal
  have values := congrArg Fin.val equal
  simp only at values
  omega

theorem CertifiedReplacement.response_reflection
    {candidate : Candidate ctx stub}
    (certificate : CertifiedReplacement ctx stub candidate)
    {left right : ctx.G.Vertex}
    (returnPath : ctx.G.object.graph.Walk left right)
    (returnIsPath : returnPath.IsPath) :
    PowerOfTwoLength (candidate.1.1 + returnPath.length) ↔
      PowerOfTwoLength (sourceLength ctx stub + returnPath.length) := by
  let coordinate := coordinateOfReturn ctx returnPath returnIsPath
  have same := certificate.sameResponse coordinate
  rw [← response_reflects_actualReturn ctx candidate.1.1 returnPath returnIsPath,
    ← response_reflects_actualReturn ctx (sourceLength ctx stub) returnPath
      returnIsPath]
  exact Bool.eq_iff_iff.mp same

def replacementOfCompression
    {vector : CT3.ExactVectorState (spec ctx stub) (input ctx stub)}
    (certificate : CT3.CompressionCertificate (spec ctx stub)
      (capability ctx stub) (input ctx stub) vector) :
    CertifiedReplacement ctx stub certificate.candidate where
  positive := certificate.candidate.2.1
  shorter := certificate.candidate.2.2
  sameResponse := certificate.valid.2.2

def replacementOfKnownRow
    {table : CT3.ExactTableState (spec ctx stub) (capability ctx stub)}
    (certificate : CT3.KnownRowCertificate (spec ctx stub)
      (capability ctx stub) (input ctx stub) table) :
    CertifiedReplacement ctx stub certificate.row where
  positive := certificate.row.2.1
  shorter := certificate.row.2.2
  sameResponse := by
    intro coordinate
    exact (certificate.rowMatches coordinate).symm

/-- All CT3 terminals are retained without erasure.  Both compression and an
exact known row yield a certified canonical replacement; table defects and
novel source vectors remain their concrete CT3 residuals. -/
inductive Routed where
  | replacement (candidate : Candidate ctx stub)
      (certificate : CertifiedReplacement ctx stub candidate)
  | distinguishing
      (residual : CT3.DistinguishingContextResidual
        (spec ctx stub) (capability ctx stub) (input ctx stub))
  | novel {table : CT3.ExactTableState (spec ctx stub) (capability ctx stub)}
      (residual : CT3.NovelExternalTypeResidual
        (spec ctx stub) (capability ctx stub) (input ctx stub) table)

noncomputable def routeOutcome
    {terminal : CT3.Graph.Terminal}
    (outcome : CT3.RawOutcome (spec ctx stub) (capability ctx stub)
      (input ctx stub) terminal) : Routed ctx stub :=
  match outcome with
  | .compression certificate =>
      .replacement certificate.candidate
        (replacementOfCompression ctx stub certificate)
  | .distinguishing residual => .distinguishing residual
  | .knownRow certificate =>
      .replacement certificate.row (replacementOfKnownRow ctx stub certificate)
  | .novelRow residual => .novel residual

noncomputable def route : Routed ctx stub :=
  routeOutcome ctx stub (run ctx stub).outcome

theorem run_verified : CT3.OutcomeClaim (run ctx stub).outcome :=
  CT3.run_verified (spec ctx stub) (capability ctx stub) (input ctx stub)

theorem run_traceValid :
    @CT3.Graph.ValidTrace PackedProblem.{u} (spec ctx stub)
      (capability ctx stub) (input ctx stub) (run ctx stub).trace :=
  CT3.run_trace_valid (spec ctx stub) (capability ctx stub) (input ctx stub)

theorem run_polynomial :
    CT3.localCheckBound (coordinates ctx) (candidates ctx stub)
      (candidates ctx stub) ≤
        8 * (ctx.G.object.input.vertices.card + 1) ^ 2 :=
  workBound ctx stub

theorem route_exhaustive :
    (∃ candidate certificate,
      route ctx stub = .replacement candidate certificate) ∨
    (∃ residual, route ctx stub = .distinguishing residual) ∨
    (∃ table residual, route ctx stub = @Routed.novel ctx stub table residual) := by
  cases equation : route ctx stub with
  | replacement candidate certificate =>
      exact Or.inl ⟨candidate, certificate, rfl⟩
  | distinguishing residual => exact Or.inr (Or.inl ⟨residual, rfl⟩)
  | novel residual => exact Or.inr (Or.inr ⟨_, residual, rfl⟩)

/-- CT3 promotion indexed by the exact bounded germ residual produced by the
graph-owned scale split. -/
inductive RoutedShort
    (germ : Producer.ColdStructuralGerm
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
    (threshold : Nat)
    (_short : BoundedSameInterfaceResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub germ threshold) where
  | replacement (candidate : Candidate ctx stub)
      (certificate : CertifiedReplacement ctx stub candidate)
  | distinguishing
      (residual : CT3.DistinguishingContextResidual
        (spec ctx stub) (capability ctx stub) (input ctx stub))
  | novel {table : CT3.ExactTableState (spec ctx stub) (capability ctx stub)}
      (residual : CT3.NovelExternalTypeResidual
        (spec ctx stub) (capability ctx stub) (input ctx stub) table)

/-- Execute CT3 from the actual short residual.  The residual is an inherited
index; it does not contribute candidates, responses, or a selected result. -/
noncomputable def routeShort
    (germ : Producer.ColdStructuralGerm
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
    (threshold : Nat)
    (short : BoundedSameInterfaceResidual
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub germ threshold) : RoutedShort ctx stub germ threshold short :=
  match route ctx stub with
  | .replacement candidate certificate => .replacement candidate certificate
  | .distinguishing residual => .distinguishing residual
  | .novel residual => .novel residual

end Erdos64EG.Internal.P13ShortPathCT3
