import Erdos64EG.Future.CT12TypeBCompletion
import Erdos64EG.Future.CT12TypeBDemandReachability

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT12: exact minimal Type B overlap support

This file is the obstruction branch of the unconditional CT12 alternative.
The obstruction, its minimality, and its support are projections of the
framework theorem.  The support is the union of each selected demand's
declared finite carrier universe, so a demand blocked by the ordinary reserve
cannot disappear merely because its valid candidate fibre is empty.
-/

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

/-- A proof-carrying minimal obstruction selected from the exact demand
schedule. -/
structure MinimalOverlap where
  selected : List support.Demand
  sublist : selected.Sublist support.completionProfile.fullSchedule
  minimal : support.completionProfile.MinimalOverlapObstruction selected

namespace MinimalOverlap

variable {support : TypeBAssignedSupport ctx}
  (obstruction : support.MinimalOverlap)

noncomputable def carrierSet : Set ctx.G.Vertex :=
  support.completionProfile.overlapSupport obstruction.selected

theorem nonempty_demands : obstruction.selected ≠ [] :=
  obstruction.minimal.obstruction.nonempty

theorem no_disjoint_choice :
    ¬Nonempty (support.completionProfile.Choice obstruction.selected) :=
  obstruction.minimal.obstruction.noChoice

theorem proper_subschedule_has_choice
    (smaller : List support.Demand)
    (sublist : smaller.Sublist obstruction.selected)
    (nonempty : smaller ≠ [])
    (shorter : smaller.length < obstruction.selected.length) :
    Nonempty (support.completionProfile.Choice smaller) :=
  obstruction.minimal.properChoice smaller sublist nonempty shorter

/-- The minimal obstruction cannot split into two nonempty scheduled blocks
whose complete declared carrier universes are disjoint across the split. -/
theorem no_separated_carrier_partition :
    support.completionProfile.SeparatedPartition obstruction.selected → False :=
  obstruction.minimal.no_separatedPartition

/-- The selected demands form one connected component under literal declared-
carrier intersection.  This is derived from minimal obstruction, not carried
as an application certificate. -/
theorem demandInteraction_connected
    (start target : support.Demand)
    (start_mem : start ∈ obstruction.selected)
    (target_mem : target ∈ obstruction.selected) :
    support.completionProfile.InteractionReachable obstruction.selected
      start target :=
  Core.FiniteRefinedLedger.Profile.MinimalOverlapObstruction.interaction_connected
    (profile := support.completionProfile) obstruction.minimal
    start target start_mem target_mem

/-- Centers of demands in the minimal obstruction are connected by actual
ambient graph paths obtained by chaining intersecting local carrier supports. -/
theorem centers_reachable
    (start target : support.Demand)
    (start_mem : start ∈ obstruction.selected)
    (target_mem : target ∈ obstruction.selected) :
    ctx.G.object.graph.Reachable start.1 target.1 := by
  have chain := obstruction.demandInteraction_connected start target
    start_mem target_mem
  induction chain with
  | refl _ => exact SimpleGraph.Reachable.rfl
  | @step left right _previousChain _right_mem interacts previous =>
      rcases Finset.not_disjoint_iff.mp interacts with
        ⟨carrier, carrierLeft, carrierRight⟩
      exact (previous _previousChain.target_mem).trans
        ((support.demandSupport_reachable left carrierLeft).trans
          (support.demandSupport_reachable right carrierRight).symm)

/-- Every carrier in the obstruction support is ambiently reachable from any
selected demand center. -/
theorem carrier_reachable_from_center
    (start : support.Demand)
    (start_mem : start ∈ obstruction.selected)
    {carrier : ctx.G.Vertex}
    (carrier_mem : carrier ∈ obstruction.carrierSet) :
    ctx.G.object.graph.Reachable start.1 carrier := by
  rcases (support.completionProfile.mem_overlapSupport_iff
    obstruction.selected carrier).1 carrier_mem with
    ⟨demand, demand_mem, local_mem⟩
  exact (obstruction.centers_reachable start demand start_mem demand_mem).trans
    (support.demandSupport_reachable demand local_mem)

/-- The complete overlap carrier set lies in one ambient graph component.
This is the exact connectivity consequence available from local fan paths and
minimal carrier interaction. -/
theorem carrierSet_pairwise_reachable
    {left right : ctx.G.Vertex}
    (left_mem : left ∈ obstruction.carrierSet)
    (right_mem : right ∈ obstruction.carrierSet) :
    ctx.G.object.graph.Reachable left right := by
  cases selected_eq : obstruction.selected with
  | nil =>
      exact False.elim (obstruction.nonempty_demands selected_eq)
  | cons start tail =>
      let startDemand : support.Demand := start
      have start_mem : startDemand ∈ obstruction.selected := by
        rw [selected_eq]
        simp [startDemand]
      exact (obstruction.carrier_reachable_from_center startDemand start_mem
        left_mem).symm.trans
          (obstruction.carrier_reachable_from_center startDemand start_mem
            right_mem)

/-- Every scheduled center is literally present in the overlap carrier set,
independently of candidate-fibre inhabitation. -/
theorem center_mem_carrierSet {demand : support.Demand}
    (member : demand ∈ obstruction.selected) :
    demand.1 ∈ obstruction.carrierSet := by
  apply (support.completionProfile.mem_overlapSupport_iff
    obstruction.selected demand.1).2
  exact ⟨demand, member, support.demand_center_mem_declaredSupport demand⟩

/-- Contextual dyadic safety is inherited without a local contract: the
ambient minimal counterexample itself avoids the target. -/
theorem ambient_dyadic_safe : ¬Target ctx.G.object :=
  (packedStaticInput.fixedContext ctx).avoids

/-- Distinct demand centers are nonadjacent, derived from deletion
criticality and their literal high-center witnesses. -/
theorem centers_not_adjacent {left right : support.Demand}
    : ¬ctx.G.object.graph.Adj left.1 right.1 := by
  have leftHigh : 4 ≤ ctx.G.object.degree left.1 := by
    rw [← support.entry_center left]
    cases support.entry left with
    | certificate marked => exact marked.centerHigh
    | positive entry => exact entry.centerHigh
  have rightHigh : 4 ≤ ctx.G.object.degree right.1 := by
    rw [← support.entry_center right]
    cases support.entry right with
    | certificate marked => exact marked.centerHigh
    | positive entry => exact entry.centerHigh
  intro adjacent
  have rightCubic :=
    sparseSurplus_highCenter_neighbor_cubic ctx leftHigh adjacent
  omega

/-- Every neighbour of a demand center has ambient degree three. -/
theorem center_neighbor_cubic (demand : support.Demand)
    {neighbor : ctx.G.Vertex}
    (adjacent : ctx.G.object.graph.Adj demand.1 neighbor) :
    ctx.G.object.degree neighbor = 3 := by
  have centerHigh : 4 ≤ ctx.G.object.degree demand.1 := by
    rw [← support.entry_center demand]
    cases support.entry demand with
    | certificate marked => exact marked.centerHigh
    | positive entry => exact entry.centerHigh
  exact sparseSurplus_highCenter_neighbor_cubic ctx centerHigh adjacent

/-- Every literal same-window datum carried by the obstruction remains subject
to the already verified direct-cycle exclusion. -/
theorem sameWindow_directCycleFree
    {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph}
    (pair : Graph.FanWindowCycle.ClosedPair path) :
    Graph.FanWindowCycle.DirectCycleFree PowerOfTwoLength pair :=
  Graph.FanWindowCycle.directCycleFree_of_avoids
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).avoids pair

/-- The corresponding two-window exclusion is likewise ambient and needs no
obstruction certificate field. -/
theorem twoWindow_directCycleFree
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g ctx.G.object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g ctx.G.object.graph}
    (data : Graph.TwoWindowCycle.Data firstPath secondPath) :
    Graph.TwoWindowCycle.DirectCycleFree PowerOfTwoLength data :=
  Graph.TwoWindowCycle.directCycleFree_of_avoids PowerOfTwoLength
    (packedStaticInput.fixedContext ctx).avoids data

/-- Any literal nonempty-boundary proper compression associated with the
overlap support is impossible by the graph-owned CT3 gluing theorem.  The
boundaried atom and compression are concrete graph structures, not response
flags supplied by the obstruction. -/
theorem proper_compression_impossible
    {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : ConcreteCT3.ProperAtom ctx boundaries)
    (compression : ConcreteCT3.Compression atom) : False :=
  (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
    packedStaticInput boundaries ctx).compressionImpossible atom compression

end MinimalOverlap

/-- Failure of the full B2 disjoint choice yields a literal minimal overlap
obstruction; this is the contrapositive branch used by the manuscript. -/
noncomputable def minimalOverlap_of_no_fullChoice
    (failure : ¬Nonempty support.completionProfile.FullChoice) :
    support.MinimalOverlap := by
  apply Classical.choice
  have existsObstruction : Nonempty support.MinimalOverlap := by
    rcases support.full_choice_or_minimal_obstruction with choice | obstruction
    · exact False.elim (failure choice)
    · exact ⟨⟨obstruction.choose, obstruction.choose_spec.1,
          obstruction.choose_spec.2⟩⟩
  exact existsObstruction

end TypeBAssignedSupport

/-- Same-CT12 theorem extension exposing both sides of the exact B2
alternative.  The completed CT12 ledger remains the literal predecessor. -/
abbrev VerifiedTypeBOverlapSupportPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTypeBCompletionPrefix ctx)
    (fun _previous => ∀ support : TypeBAssignedSupport ctx,
      ¬Nonempty support.completionProfile.FullChoice →
        Nonempty support.MinimalOverlap)

noncomputable def verifiedTypeBOverlapSupportPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBCompletionPrefix ctx) :
    VerifiedTypeBOverlapSupportPrefix ctx :=
  ⟨previous, fun support failure =>
    ⟨support.minimalOverlap_of_no_fullChoice failure⟩⟩

theorem exists_verifiedTypeBOverlapSupportPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBOverlapSupportPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTypeBCompletionPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBOverlapSupportPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
