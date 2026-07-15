import Erdos64EG.CT14P13PositiveDeficiency
import StructuralExhaustion.Graph.FiniteSupportResponse
import StructuralExhaustion.Graph.InducedPathWindowLedger
import StructuralExhaustion.Graph.ClosedRankDrop
import StructuralExhaustion.Graph.OneThreeRepair

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u v

/-!
# Exact remainder incidence, wedge, and curvature-rank stage

This file implements diagram nodes `[29]`--`[35]`.  The input is exactly the
node-`[28]` remainder on the selected minimal counterexample.  The graph layer
counts its boundary incidences and length-two wedges.  CT15 then scans the
literal wedge-coordinate family.  Admissible rank quotients are the framework
quotients with certified reductions, so minimality makes every such quotient
injective and the exact run reaches the full-rank ledger.
-/

abbrev RemainderCurvatureProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.PositiveDeficiencyWedge.Profile ctx.G.object

noncomputable def p13RemainderCurvatureProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    RemainderCurvatureProfile ctx :=
  Graph.InducedPathWindowLedger.remainderDeficiencyProfile ctx.G.object

theorem p13Curvature_positiveDeficiency_eq_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency =
      (p13RemainderDeficiencyProfile ctx).positiveDeficiency := by
  rfl

/-- Node `[29]`: every positive-deficiency unit is paid by a literal
window--remainder incidence, and the complete selected-window token ledger has
the exact `15p+σ_W` cardinality. -/
theorem p13Remainder_positiveDeficiency_le_windowTokens
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      Graph.InducedPathWindowLedger.tokenCount ctx.G.object :=
  Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_tokenCount
    ctx.G.object (fun vertex =>
      ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))

theorem p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object :=
  Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus
      ctx.G.object (fun vertex =>
        ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))

theorem p13Remainder_surplusAdjustedDeficiency
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object :=
  Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le
    ctx.G.object (fun vertex =>
      ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))

/-- Node `[30]`: exact finite wedge floor before normalization. -/
theorem p13Remainder_wedgeFloor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    3 * (p13RemainderVertices ctx).card -
        2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  (p13RemainderCurvatureProfile ctx).wedgeFloor

/-! ## Literal raw length-two coordinates -/

@[implicit_reducible]
noncomputable def p13RemainderVertexEnumeration
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (P13RemainderVertex ctx) :=
  Core.Enumeration.subtype ctx.G.object.input.vertices
    (fun vertex => vertex ∈ p13RemainderVertices ctx)
    (fun _vertex => by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      infer_instance)

abbrev P13InternalNeighbor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : P13RemainderVertex ctx) :=
  {vertex : ctx.G.Vertex //
    vertex ∈ p13RemainderVertices ctx ∧
      ctx.G.object.graph.Adj center.1 vertex}

@[implicit_reducible]
noncomputable def p13InternalNeighborEnumeration
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : P13RemainderVertex ctx) :
    FinEnum (P13InternalNeighbor ctx center) :=
  Core.Enumeration.subtype ctx.G.object.input.vertices
    (fun vertex => vertex ∈ p13RemainderVertices ctx ∧
      ctx.G.object.graph.Adj center.1 vertex)
    (fun _vertex => by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      letI : DecidableRel ctx.G.object.graph.Adj :=
        ctx.G.object.input.decideAdj
      infer_instance)

/-- One raw internal length-two wedge: a remainder center and an unordered
pair represented in the canonical neighbour order. -/
abbrev P13CurvatureCoordinate
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun center : P13RemainderVertex ctx =>
    Core.Enumeration.OrderedDistinctPair
      (p13InternalNeighborEnumeration ctx center)

@[implicit_reducible]
noncomputable def p13CurvatureCoordinates
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (P13CurvatureCoordinate ctx) := by
  letI : FinEnum (P13RemainderVertex ctx) :=
    p13RemainderVertexEnumeration ctx
  letI (center : P13RemainderVertex ctx) :
      FinEnum (P13InternalNeighbor ctx center) :=
    p13InternalNeighborEnumeration ctx center
  letI (center : P13RemainderVertex ctx) : FinEnum
      (Core.Enumeration.OrderedDistinctPair
        (p13InternalNeighborEnumeration ctx center)) :=
    Core.Enumeration.orderedDistinctPairs
      (p13InternalNeighborEnumeration ctx center)
  exact inferInstance

theorem p13InternalNeighbor_card
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (center : P13RemainderVertex ctx) :
    (p13InternalNeighborEnumeration ctx center).card =
      (p13RemainderCurvatureProfile ctx).internalDegree center.1 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  letI : FinEnum (P13InternalNeighbor ctx center) :=
    p13InternalNeighborEnumeration ctx center
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]
  unfold Graph.PositiveDeficiencyWedge.Profile.internalDegree
  apply congrArg Finset.card
  ext vertex
  simp [p13RemainderCurvatureProfile,
    Graph.InducedPathWindowLedger.remainderDeficiencyProfile,
    p13RemainderVertices, SimpleGraph.mem_neighborFinset, and_comm]

theorem p13CurvatureCoordinates_card_eq_wedgeCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CurvatureCoordinates ctx).card =
      (p13RemainderCurvatureProfile ctx).wedgeCount := by
  letI : FinEnum (P13RemainderVertex ctx) :=
    p13RemainderVertexEnumeration ctx
  letI (center : P13RemainderVertex ctx) :
      FinEnum (P13InternalNeighbor ctx center) :=
    p13InternalNeighborEnumeration ctx center
  letI (center : P13RemainderVertex ctx) : FinEnum
      (Core.Enumeration.OrderedDistinctPair
        (p13InternalNeighborEnumeration ctx center)) :=
    Core.Enumeration.orderedDistinctPairs
      (p13InternalNeighborEnumeration ctx center)
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_sigma]
  simp_rw [← FinEnum.card_eq_fintypeCard,
    Core.Enumeration.orderedDistinctPairs_card,
    p13InternalNeighbor_card]
  unfold Graph.PositiveDeficiencyWedge.Profile.wedgeCount
  change (∑ center : P13RemainderVertex ctx,
      Nat.choose
        ((p13RemainderCurvatureProfile ctx).internalDegree center.1) 2) = _
  have coreEq : (p13RemainderCurvatureProfile ctx).core =
      p13RemainderVertices ctx := by
    rfl
  calc
    (∑ center : P13RemainderVertex ctx,
        Nat.choose
          ((p13RemainderCurvatureProfile ctx).internalDegree center.1) 2) =
      ∑ center ∈ (p13RemainderVertices ctx).attach,
        Nat.choose
          ((p13RemainderCurvatureProfile ctx).internalDegree center.1) 2 := by
      simp only [Finset.attach_eq_univ]
      rfl
    _ = ∑ vertex ∈ p13RemainderVertices ctx,
        Nat.choose
          ((p13RemainderCurvatureProfile ctx).internalDegree vertex) 2 := by
      simpa using Finset.sum_attach (p13RemainderVertices ctx)
        (fun vertex => Nat.choose
          ((p13RemainderCurvatureProfile ctx).internalDegree vertex) 2)
    _ = ∑ vertex ∈ (p13RemainderCurvatureProfile ctx).core,
        Nat.choose
          ((p13RemainderCurvatureProfile ctx).internalDegree vertex) 2 := by
      rw [coreEq]

theorem p13CurvatureCoordinates_card_le_cube
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CurvatureCoordinates ctx).card ≤
      ctx.G.object.input.vertices.card ^ 3 := by
  rw [p13CurvatureCoordinates_card_eq_wedgeCount]
  exact (p13RemainderCurvatureProfile ctx).wedgeCount_le_cube

noncomputable def p13CurvatureSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (coordinate : P13CurvatureCoordinate ctx) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact { coordinate.1.1,
    (Core.Enumeration.OrderedDistinctPair.first coordinate.2).1,
    (Core.Enumeration.OrderedDistinctPair.second coordinate.2).1 }

/-- Node `[31]`: exact response profile of every raw wedge coordinate. -/
noncomputable def p13CurvatureResponseProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.FiniteSupportResponse.Profile packedStaticInput ctx
      (P13CurvatureCoordinate ctx) where
  coordinates := p13CurvatureCoordinates ctx
  support := p13CurvatureSupport

noncomputable def runP13CurvatureCT15
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (p13CurvatureResponseProfile ctx).run

/-- Nodes `[32]` and `[34]`: the exact CT15 split reaches full rank. -/
theorem runP13CurvatureCT15_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13CurvatureCT15 ctx).terminal = .fullRankLedger :=
  (p13CurvatureResponseProfile ctx).terminal

theorem runP13CurvatureCT15_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runP13CurvatureCT15 ctx).trace =
      [.entry, .rankComputation, .rankSplit, .ledgerComputation,
        .ledgerComparison, .fullRankLedgerTerminal] :=
  (p13CurvatureResponseProfile ctx).trace

theorem p13Curvature_fullRank_eq_wedgeCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  p13CurvatureCoordinates_card_eq_wedgeCount ctx

/-- Nodes `[33]` and `[35]`: the rank-reducing residual is an exact empty
branch, because every admitted quotient is injective by certified reduction
and minimality. -/
theorem no_p13Curvature_rankDrop
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ¬∃ coordinate : P13CurvatureCoordinate ctx,
      CT15.AdmissibleQuotient.TargetDependent ctx
        (p13CurvatureResponseProfile ctx).responseSystem coordinate := by
  rintro ⟨coordinate, dependent⟩
  exact CT15.AdmissibleQuotient.not_targetDependent ctx
    (p13CurvatureResponseProfile ctx).responseSystem coordinate dependent

structure VerifiedP13CurvaturePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13PositiveDeficiencyPrefix ctx
  incidenceSupply :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object
  surplusAdjustedSupply :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object
  wedgeFloor :
    3 * (p13RemainderVertices ctx).card -
        2 * (p13RemainderCurvatureProfile ctx).positiveDeficiency ≤
      (p13RemainderCurvatureProfile ctx).wedgeCount
  coordinateCount :
    (p13CurvatureCoordinates ctx).card =
      (p13RemainderCurvatureProfile ctx).wedgeCount
  coordinateCubic :
    (p13CurvatureCoordinates ctx).card ≤
      ctx.G.object.input.vertices.card ^ 3
  terminal : (runP13CurvatureCT15 ctx).terminal = .fullRankLedger
  trace : (runP13CurvatureCT15 ctx).trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal]
  noRankDrop : ¬∃ coordinate : P13CurvatureCoordinate ctx,
    CT15.AdmissibleQuotient.TargetDependent ctx
      (p13CurvatureResponseProfile ctx).responseSystem coordinate
  polynomial :
    (p13CurvatureResponseProfile ctx).ct15Profile.budget.checks () ≤
      (p13CurvatureResponseProfile ctx).ct15Profile.budget.coefficient *
        ((p13CurvatureResponseProfile ctx).ct15Profile.budget.size () + 1) ^
          (p13CurvatureResponseProfile ctx).ct15Profile.budget.degree

noncomputable def verifiedP13CurvaturePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PositiveDeficiencyPrefix ctx) :
    VerifiedP13CurvaturePrefix ctx where
  previous := previous
  incidenceSupply :=
    p13Remainder_positiveDeficiency_le_fifteen_mul_packing_add_surplus ctx
  surplusAdjustedSupply := p13Remainder_surplusAdjustedDeficiency ctx
  wedgeFloor := p13Remainder_wedgeFloor ctx
  coordinateCount := p13CurvatureCoordinates_card_eq_wedgeCount ctx
  coordinateCubic := p13CurvatureCoordinates_card_le_cube ctx
  terminal := runP13CurvatureCT15_terminal ctx
  trace := runP13CurvatureCT15_trace ctx
  noRankDrop := no_p13Curvature_rankDrop ctx
  polynomial := (p13CurvatureResponseProfile ctx).linearWork

/-! ## Nodes `[40]`--`[42]`: proper enlarged-support closure -/

abbrev ProperDelocalizationAtom
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T] :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.Atom
    packedStaticInput boundaries ctx

abbrev ProperDelocalizationLocation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type v) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.Location
    packedStaticInput boundaries original Whole

abbrev ProperDelocalizationRouted
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type v) :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.Routed
    packedStaticInput boundaries original Whole

/-- Nodes `[40]`--`[42]` consume the enlarged-support payload returned by the
green node-`[39]` route.  Proper supports close through the literal CT3 audit;
only the unchanged whole-graph payload can continue to node `[43]`. -/
def routeProperDelocalization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type v)
    (location : ProperDelocalizationLocation ctx boundaries original Whole) :
    ProperDelocalizationRouted ctx boundaries original Whole :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.route
    packedStaticInput boundaries original Whole location

/-- The literal nodes-`[36]`--`[42]` composition: the only enlarged payload
accepted from the rank-drop CT is the exact proper/whole value consumed by the
delocalization CT. -/
def routeRankDropThroughProperDelocalization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type v)
    (certificate :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate
        packedStaticInput boundaries original
          (ProperDelocalizationLocation ctx boundaries original Whole)) :
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.CombinedRouted
      packedStaticInput boundaries original Whole :=
  Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.routeAfterRankDrop
    packedStaticInput boundaries original Whole certificate

structure VerifiedP13ProperDelocalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13CurvaturePrefix ctx
  rankDropStage : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Enlarged : Type u),
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.VerifiedStage
      packedStaticInput boundaries original Enlarged
  stage : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type u),
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.VerifiedStage
      packedStaticInput boundaries
        original Whole
  combined : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) (Whole : Type u)
    (_certificate :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate
        packedStaticInput boundaries original
          (ProperDelocalizationLocation ctx boundaries original Whole)),
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.CombinedRouted
      packedStaticInput boundaries original Whole

def verifiedP13ProperDelocalizationPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13CurvaturePrefix ctx) :
    VerifiedP13ProperDelocalizationPrefix ctx where
  previous := previous
  rankDropStage := fun boundaries _instance original Enlarged =>
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.verifiedStage
      packedStaticInput boundaries original Enlarged
  stage := fun boundaries _instance original Whole =>
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.verifiedStage
      packedStaticInput boundaries
        original Whole
  combined := fun boundaries _instance original Whole certificate =>
    routeRankDropThroughProperDelocalization ctx boundaries original Whole certificate

/-! ## Nodes `[43]`--`[47]`: whole-support barrier and full-rank join -/

abbrev P13ClosedProposal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  CT15.AdmissibleQuotient.Proposal
    (p13CurvatureResponseProfile ctx).responseSystem

/-- Exact payload retained by the node-`[41]` whole-support constructor.  The
quotient is the admitted proposal produced by the finite determination
certificate, and the two coordinates are the literal rank-drop witness. -/
structure P13WholeDelocalization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Type (u + 2) where
  proposal : P13ClosedProposal ctx
  quotient : CT15.AdmissibleQuotient.Admissible ctx
    (p13CurvatureResponseProfile ctx).responseSystem proposal
  left : P13CurvatureCoordinate ctx
  right : P13CurvatureCoordinate ctx
  distinct : left ≠ right
  identified : proposal.Identifies left right

/-- Node `[45]`: the already-admitted whole-support proposal has exact labels.
The response and representative obligations were discharged by the finite
quotient-admission contract and are not recomputed here. -/
theorem p13ClosedRankDrop_exactBarrier
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (proposal : P13ClosedProposal ctx)
    (quotient : CT15.AdmissibleQuotient.Admissible ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal) :
    Graph.ClosedRankDrop.ExactBarrier ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal :=
  Graph.ClosedRankDrop.exactBarrier quotient

/-- Node `[45]`: distinct raw curvature labels cannot be silently merged by
an admitted quotient. -/
theorem no_p13Closed_silentIdentification
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (proposal : P13ClosedProposal ctx)
    (quotient : CT15.AdmissibleQuotient.Admissible ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal)
    {left right : P13CurvatureCoordinate ctx} (distinct : left ≠ right)
    (identified : proposal.Identifies left right) : False :=
  Graph.ClosedRankDrop.no_silent_identification quotient distinct identified

/-- Node `[46]`: the whole-support rank-drop payload is contradictory. -/
theorem p13WholeDelocalization_impossible
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (payload : P13WholeDelocalization ctx) : False :=
  no_p13Closed_silentIdentification ctx payload.proposal payload.quotient
    payload.distinct payload.identified

def P13GlobalRankDropRouted
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries) : Prop :=
  (∃ realization : Graph.PackedBoundariedGluing.Piece T,
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective
      packedStaticInput boundaries realization original.source) ∨
  (∃ (source realization : Graph.PackedBoundariedGluing.Piece T),
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective
      packedStaticInput boundaries realization source)

/-- Literal composition of nodes `[36]`--`[45]`: the whole constructor from
the proper-support route carries exactly the closed proposal consumed here. -/
def routeRankDropThroughGlobalClosure
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries)
    (certificate :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate
        packedStaticInput boundaries original
          (ProperDelocalizationLocation ctx boundaries original
            (P13WholeDelocalization ctx))) :
    P13GlobalRankDropRouted ctx boundaries original := by
  rcases routeRankDropThroughProperDelocalization ctx boundaries original
      (P13WholeDelocalization ctx) certificate with earlyDefect | routedExists
  · exact Or.inl earlyDefect
  · rcases routedExists with ⟨routed⟩
    cases routed with
    | properClosed extension defective =>
        exact Or.inr
          ⟨extension.enlarged.source, extension.realization, defective⟩
    | whole payload =>
        exact False.elim (p13WholeDelocalization_impossible ctx payload)

/-- Node `[44]`: the exact one--three repair identity over integers. -/
theorem oneThreeRepair_identity
    (internalVertices boundaryLeaves internalEdges cycleRank surplus : Int)
    (handshake :
      3 * internalVertices + surplus + boundaryLeaves =
        2 * (internalEdges + boundaryLeaves))
    (cycleRankEq : cycleRank = internalEdges - internalVertices + 1) :
    internalVertices =
      boundaryLeaves - 2 + 2 * cycleRank - surplus :=
  Core.OneThreeRepair.identity internalVertices boundaryLeaves internalEdges
    cycleRank surplus handshake cycleRankEq

/-- Graph-owned form of node `[44]`: all five quantities are computed from
the same finite connected repair component. -/
theorem oneThreeRepair_component_identity {V : Type u}
    (component : Graph.OneThreeRepair.Component V) :
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank -
        component.surplus :=
  component.identity

/-- Complete global rank-drop block and node-`[47]` join. -/
structure VerifiedP13GlobalRankClosurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13ProperDelocalizationPrefix ctx
  combinedGlobal : ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (original : ProperDelocalizationAtom ctx boundaries)
    (_certificate :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate
        packedStaticInput boundaries original
          (ProperDelocalizationLocation ctx boundaries original
            (P13WholeDelocalization ctx))),
    P13GlobalRankDropRouted ctx boundaries original
  closedBarrier : ∀ (proposal : P13ClosedProposal ctx)
    (_quotient : CT15.AdmissibleQuotient.Admissible ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal),
    Graph.ClosedRankDrop.ExactBarrier ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal
  noSilentIdentification : ∀ (proposal : P13ClosedProposal ctx)
    (_quotient : CT15.AdmissibleQuotient.Admissible ctx
      (p13CurvatureResponseProfile ctx).responseSystem proposal)
    {left right : P13CurvatureCoordinate ctx}, left ≠ right →
      proposal.Identifies left right → False
  wholeRankDropClosed : ∀ _payload : P13WholeDelocalization ctx, False
  repairIdentity : ∀ internalVertices boundaryLeaves internalEdges
    cycleRank surplus : Int,
    3 * internalVertices + surplus + boundaryLeaves =
        2 * (internalEdges + boundaryLeaves) →
      cycleRank = internalEdges - internalVertices + 1 →
        internalVertices =
          boundaryLeaves - 2 + 2 * cycleRank - surplus
  graphRepairIdentity : ∀ {V : Type u}
    (component : Graph.OneThreeRepair.Component V),
      (component.internal.card : Int) =
        component.boundary.card - 2 + 2 * component.cycleRank -
          component.surplus
  fullRankCount :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount
  fullRankTerminal : (runP13CurvatureCT15 ctx).terminal = .fullRankLedger
  constantClosedAudit : Graph.ClosedRankDrop.checks = 1

def verifiedP13GlobalRankClosurePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13ProperDelocalizationPrefix ctx) :
    VerifiedP13GlobalRankClosurePrefix ctx where
  previous := previous
  combinedGlobal := routeRankDropThroughGlobalClosure ctx
  closedBarrier := p13ClosedRankDrop_exactBarrier ctx
  noSilentIdentification := no_p13Closed_silentIdentification ctx
  wholeRankDropClosed := p13WholeDelocalization_impossible ctx
  repairIdentity := oneThreeRepair_identity
  graphRepairIdentity := oneThreeRepair_component_identity
  fullRankCount := p13Curvature_fullRank_eq_wedgeCount ctx
  fullRankTerminal := runP13CurvatureCT15_terminal ctx
  constantClosedAudit := Graph.ClosedRankDrop.checks_eq_one

theorem exists_verifiedP13CurvaturePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedP13CurvaturePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13PositiveDeficiencyPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedP13CurvaturePrefix ctx previous⟩

theorem exists_verifiedP13ProperDelocalizationPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedP13ProperDelocalizationPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13CurvaturePrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedP13ProperDelocalizationPrefix ctx previous⟩

theorem exists_verifiedP13GlobalRankClosurePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedP13GlobalRankClosurePrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13ProperDelocalizationPrefix object baseline avoids
  exact ⟨ctx, rankLe,
    verifiedP13GlobalRankClosurePrefix ctx previous⟩

end Erdos64EG.Internal
