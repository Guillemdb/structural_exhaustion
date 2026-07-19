import Erdos64EG.CT14LocalB1Entry
import StructuralExhaustion.Graph.HybridFanCandidate

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: concrete positive-deficit Type B candidate fibre

The candidate items are the literal cubic-closed incidences already verified
by the CT14 B1 stage.  Window incidences are mandatory, selected non-window
incidences must pay the exact remaining demand, and an incidence already used
by the ordinary reserve is forbidden.  This is the positive branch of
`def:typeB-candidate-ledger`; no candidate-validity predicate is supplied by
the application.
-/

namespace PositiveDeficitMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (entry : PositiveDeficitMarkedFan ctx)

abbrev TypeBIncidenceReserve
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.HybridFanCandidate.IncidenceReserve ctx.G.Vertex

noncomputable def candidateProfile (reserve : TypeBIncidenceReserve ctx) :=
  Graph.HybridFanCandidate.profile
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) reserve

abbrev Candidate (reserve : TypeBIncidenceReserve ctx) :=
  (entry.candidateProfile reserve).Candidate

/-- Every concrete candidate contains every packed-window incidence. -/
theorem candidate_contains_every_window (reserve : TypeBIncidenceReserve ctx)
    (candidate : entry.Candidate reserve)
    {incidence : Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)}
    (window : Graph.HybridFanIncidence.incidenceKind
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      incidence = .window) : incidence ∈ candidate.1 :=
  Graph.HybridFanCandidate.Candidate.contains_every_window
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    reserve candidate window

/-- Selected incidences are disjoint from the declared ordinary reserve by
the candidate definition itself. -/
theorem candidate_reserve_free (reserve : TypeBIncidenceReserve ctx)
    (candidate : entry.Candidate reserve)
    {incidence : Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)}
    (selected : incidence ∈ candidate.1) :
    ¬reserve.Used (Graph.HybridFanIncidence.carrier
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      incidence) :=
  Graph.HybridFanCandidate.Candidate.selected_reserve_free
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    reserve candidate selected

/-- The selected non-window half-credits pay the exact CT14 remainder. -/
theorem candidate_nonWindow_payment (reserve : TypeBIncidenceReserve ctx)
    (candidate : entry.Candidate reserve) :
    Graph.HybridFanIncidence.remainingNonWindowDemand
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable) ≤
      ∑ incidence ∈ candidate.1,
        if Graph.HybridFanIncidence.incidenceKind
            (object := ctx.G.object) (center := entry.fan.center)
            (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
            incidence = .nonWindow then 2 else 0 :=
  Graph.HybridFanCandidate.Candidate.nonWindow_payment
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    reserve candidate

/-- The mandatory window credit plus the selected non-window credit pays the
literal positive fan deficit. This is the complete local B1 inequality for an
arbitrary valid candidate, not only for the all-incidence witness. -/
theorem candidate_totalCredit_pays_deficit
    (reserve : TypeBIncidenceReserve ctx)
    (candidate : entry.Candidate reserve) :
    Graph.FanClosedPortMass.deficitNumerator
        (ctx.G.object.degree entry.fan.center)
        (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card ≤
      (Graph.HybridFanIncidence.windowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) +
      ∑ incidence ∈ candidate.1,
        if Graph.HybridFanIncidence.incidenceKind
            (object := ctx.G.object) (center := entry.fan.center)
            (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
            incidence = .nonWindow then 2 else 0 := by
  have payment := entry.candidate_nonWindow_payment reserve candidate
  unfold Graph.HybridFanIncidence.remainingNonWindowDemand at payment
  omega

/-- Every declared carrier of the positive-fan candidate fibre lies at graph
distance at most two from the actual marked center. -/
theorem declaredCarrierSupport_reachable (reserve : TypeBIncidenceReserve ctx)
    {carrier : ctx.G.Vertex}
    (member : carrier ∈ (entry.candidateProfile reserve).declaredCarrierSupport) :
    ctx.G.object.graph.Reachable entry.fan.center carrier :=
  Graph.HybridFanCandidate.declaredCarrierSupport_reachable
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    reserve member

/-- When the ordinary reserve has not consumed a local incidence, the
already-verified local B1 inequality constructs the all-incidence candidate. -/
noncomputable def reserveFreeCandidate (reserve : TypeBIncidenceReserve ctx)
    (reserveFree : ∀ incidence : Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable),
      ¬reserve.Used (Graph.HybridFanIncidence.carrier
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence)) : entry.Candidate reserve :=
  Graph.HybridFanCandidate.allItemsCandidate
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center)
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    reserve entry.degree_le_eight reserveFree

end PositiveDeficitMarkedFan

/-- The verified prefix exposes the graph-constructed positive candidate
fibre as one same-prefix theorem extension. -/
abbrev VerifiedPositiveDeficitCandidatePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedLocalB1Prefix ctx)
    (fun _previous => ∀ (entry : PositiveDeficitMarkedFan ctx)
    (reserve : PositiveDeficitMarkedFan.TypeBIncidenceReserve ctx),
    (∀ incidence : Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable),
      ¬reserve.Used (Graph.HybridFanIncidence.carrier
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence)) → Nonempty (entry.Candidate reserve))

noncomputable def verifiedPositiveDeficitCandidatePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedLocalB1Prefix ctx) :
    VerifiedPositiveDeficitCandidatePrefix ctx :=
  ⟨previous, fun entry reserve reserveFree =>
    ⟨entry.reserveFreeCandidate reserve reserveFree⟩⟩

theorem exists_verifiedPositiveDeficitCandidatePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedPositiveDeficitCandidatePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedLocalB1Prefix object baseline avoids
  exact ⟨ctx, verifiedPositiveDeficitCandidatePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
