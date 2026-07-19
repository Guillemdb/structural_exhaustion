import Erdos64EG.P13WeightedColdRestrictedD4D5
import Erdos64EG.P13WeightedColdRestrictedD6Projection
import Erdos64EG.P13WeightedColdRestrictedD7Projection
import Erdos64EG.P13WeightedColdRestrictedSurvivorFilter

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# The exact D4--D7 state at node [153]

The four clauses are kept as a labelled sum.  In particular, coincident
values never identify a D4 label with a D5, D6, or D7 label.  D7 retains its
whole symbolic outside-context response function; no outside-context family
is enumerated.

The stage runner performs the graph-derived D5 degree split and the complete
scan of the already-produced D6 ledger, but a ledger hit is retained only as
an F4 candidate.  It does not short-circuit construction of D4, D5, D6, or
D7: the manuscript tests F2 and F3 before consuming F4.  A high vertex
contributes its exact local D6 fan-center coordinate family; it is not
promoted across parts to node [61] or [64].
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

namespace D5Available

variable {package : P13WeightedColdRestrictedPrefixPackage ctx node21}
variable {stage : package.Stage}
variable (available : package.D5Available stage)
variable (ledger : package.PriorD6Ledger)

/-- The literal clause-labelled coordinate type at one stored prefix. -/
abbrev ExactD4D7Coordinate :=
  package.D4Coordinate stage ⊕
    (available.FullBaseCoordinate ⊕
      (package.DeclaredD6Coordinate ledger stage ⊕
        package.D7DeclaredCoordinate stage))

@[implicit_reducible]
noncomputable def exactD4D7Coordinates :
    FinEnum (available.ExactD4D7Coordinate ledger) := by
  letI : FinEnum (package.D4Coordinate stage) := package.d4Coordinates stage
  letI : FinEnum available.FullBaseCoordinate := available.fullBaseCoordinates
  letI : FinEnum (package.DeclaredD6Coordinate ledger stage) :=
    package.declaredD6Coordinates ledger stage
  letI : FinEnum (package.D7DeclaredCoordinate stage) :=
    package.d7DeclaredCoordinates stage
  infer_instance

/-- Exact values have one constructor per declared clause.  D5 retains its
full graph record, D6 its full dependent labelled observation and proven
semantics, and D7 the symbolic response against every supplied outside
context. -/
inductive ExactD4D7Value (ledger : package.PriorD6Ledger)
  | d4 (value : Bool)
  | d5 (value : TypeAFullD5Signature.BaseValue (V := ctx.G.Vertex))
  | d6 (value : package.ExactDeclaredD6Entry ledger)
  | d7 (response : PackedBoundariedGluing.Context ctx.G.Vertex →
      FiniteActiveInterfaceD7Signature.ExactValue (D7Stage (ctx := ctx)))

noncomputable def exactD4D7Value :
    available.ExactD4D7Coordinate ledger →
      ExactD4D7Value (package := package) ledger (ctx := ctx)
  | .inl coordinate => .d4 (package.d4Response stage coordinate)
  | .inr (.inl coordinate) => .d5 (available.fullBaseValue coordinate)
  | .inr (.inr (.inl coordinate)) =>
      .d6 (package.exactDeclaredD6Entry ledger coordinate.1)
  | .inr (.inr (.inr coordinate)) =>
      .d7 (fun outside => d7DeclaredExactValue (ctx := ctx) coordinate.1 outside)

/-- The complete local projection.  The exhaustive D6 scan is stored without
consuming its result, so an F4 candidate remains deferred until after the
manuscript's F2/F3 tests. -/
structure ExactD4D7Projection
    (d6Decision : package.D6Decision ledger stage) where
  coordinates : FinEnum (available.ExactD4D7Coordinate ledger)
  coordinatesExact : coordinates = available.exactD4D7Coordinates ledger
  value : available.ExactD4D7Coordinate ledger →
    ExactD4D7Value (package := package) ledger (ctx := ctx)
  valueExact : value = available.exactD4D7Value ledger
  priorD6Scan : package.D6Decision ledger stage
  priorD6ScanExact : priorD6Scan = d6Decision
  d6DeclaredCodes : List D6DeclaredStructuralCode
  d6DeclaredCodesExact : d6DeclaredCodes =
    package.normalizedD6DeclaredStructuralCodes ledger stage
  d6DeclaredCodesNodup : d6DeclaredCodes.Nodup
  d6DeclaredCodesFixedBound : d6DeclaredCodes.length ≤
    Fintype.card D6DeclaredKindCode * Fintype.card D6DeclaredLabelCode *
      2 ^ 28 * Fintype.card D6DeclaredValueCode
  d7FixedCodes : List FixedD7Code
  d7FixedCodesExact : d7FixedCodes = package.fixedD7Codes stage
  d7FixedCodesNodup : d7FixedCodes.Nodup
  d7FixedCodesFixedBound : d7FixedCodes.length ≤ Fintype.card FixedD7Code

noncomputable def exactD4D7Projection
    (d6Decision : package.D6Decision ledger stage) :
    available.ExactD4D7Projection ledger d6Decision where
  coordinates := available.exactD4D7Coordinates ledger
  coordinatesExact := rfl
  value := available.exactD4D7Value ledger
  valueExact := rfl
  priorD6Scan := d6Decision
  priorD6ScanExact := rfl
  d6DeclaredCodes := package.normalizedD6DeclaredStructuralCodes ledger stage
  d6DeclaredCodesExact := rfl
  d6DeclaredCodesNodup :=
    package.normalizedD6DeclaredStructuralCodes_nodup ledger stage
  d6DeclaredCodesFixedBound :=
    package.normalizedD6DeclaredStructuralCodes_length_le_fixed ledger stage
  d7FixedCodes := package.fixedD7Codes stage
  d7FixedCodesExact := rfl
  d7FixedCodesNodup := package.fixedD7Codes_nodup stage
  d7FixedCodesFixedBound := package.fixedD7Codes_length_le_alphabet stage

theorem everyD4StoredInExactProjection
    (d6Decision : package.D6Decision ledger stage)
    (coordinate : package.D4Coordinate stage) :
    (Sum.inl coordinate : available.ExactD4D7Coordinate ledger) ∈
      (available.exactD4D7Projection ledger d6Decision).coordinates.orderedValues :=
  (available.exactD4D7Projection ledger d6Decision).coordinates.mem_orderedValues _

theorem everyD5Stored (d6Decision : package.D6Decision ledger stage)
    (coordinate : available.FullBaseCoordinate) :
    (Sum.inr (Sum.inl coordinate) : available.ExactD4D7Coordinate ledger) ∈
      (available.exactD4D7Projection ledger d6Decision).coordinates.orderedValues :=
  (available.exactD4D7Projection ledger d6Decision).coordinates.mem_orderedValues _

theorem everyD6Stored (d6Decision : package.D6Decision ledger stage)
    (coordinate : package.DeclaredD6Coordinate ledger stage) :
    (Sum.inr (Sum.inr (Sum.inl coordinate)) :
      available.ExactD4D7Coordinate ledger) ∈
      (available.exactD4D7Projection ledger d6Decision).coordinates.orderedValues :=
  (available.exactD4D7Projection ledger d6Decision).coordinates.mem_orderedValues _

theorem everyD7Stored (d6Decision : package.D6Decision ledger stage)
    (coordinate : package.D7DeclaredCoordinate stage) :
    (Sum.inr (Sum.inr (Sum.inr coordinate)) :
      available.ExactD4D7Coordinate ledger) ∈
      (available.exactD4D7Projection ledger d6Decision).coordinates.orderedValues :=
  (available.exactD4D7Projection ledger d6Decision).coordinates.mem_orderedValues _

/-- The combined state stores the literal dependent D6 entry, not merely its
family tag or support.  Thus every local observation demanded by the paper is
definitionally recoverable by the later F4 consumer. -/
theorem d6Value_exact (d6Decision : package.D6Decision ledger stage)
    (coordinate : package.DeclaredD6Coordinate ledger stage) :
    (available.exactD4D7Projection ledger d6Decision).value
      (.inr (.inr (.inl coordinate))) =
        ExactD4D7Value.d6 (package.exactDeclaredD6Entry ledger coordinate.1) := by
  rfl

theorem d7Value_apply (d6Decision : package.D6Decision ledger stage)
    (coordinate : package.D7DeclaredCoordinate stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    match (available.exactD4D7Projection ledger d6Decision).value
      (.inr (.inr (.inr coordinate))) with
    | .d7 response => response outside =
        d7DeclaredExactValue (ctx := ctx) coordinate.1 outside
    | _ => False := by
  rfl

end D5Available

/-- The stage payload on the existing `[152] → [153]` edge is exactly the
locally clear payload constructed by the survivor filter.  This alias adds no
proof-flow constructor. -/
abbrev SurvivingSubcubicStage (ledger : package.PriorD6Ledger)
    (stage : package.Stage) := package.LocallyClearStage ledger stage

/-- D4--D7 projection on the only branch that the manuscript permits to enter
the finite cold state space.  An F4 result of the prior-ledger scan is stored
until the same-stage F2 and F3 negatives have been proved. -/
noncomputable def runSurvivingSubcubicStage
    (ledger : package.PriorD6Ledger) {stage : package.Stage}
    (survivor : package.SurvivingSubcubicStage ledger stage) :
    survivor.available.ExactD4D7Projection ledger
      (package.runD6 ledger stage) := by
  rw [survivor.d6Exact]
  exact survivor.available.exactD4D7Projection ledger
    (.complete survivor.priorComplete)

theorem f4_event_has_produced_origin
    (prior : ProducedPriorD6State (ctx := ctx)) (stage : package.Stage)
    (hit : package.D6F4Hit prior stage) :
    ((∃ entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx),
        hit.event = .ordinary entry) ∨
      (∃ entry : TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff
          (ctx := ctx), hit.event = .decorated entry)) ∨
      (∃ entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
          (ctx := ctx), hit.event = .routeEight entry) :=
  hit.exact_typeB_or_routeEight

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
