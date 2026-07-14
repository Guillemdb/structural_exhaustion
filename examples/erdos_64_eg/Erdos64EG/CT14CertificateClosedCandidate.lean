import Erdos64EG.CT14PositiveDeficitCandidate
import StructuralExhaustion.Graph.CertificateClosedFanCandidate

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT14: concrete certificate-closed Type B candidate fibre

The selected items are actual neighbour ports of the marked center.  Their
weights are the exact quarter-charge lower bounds already proved by CT14:
`-1` for cubic-closed members and `3` for open members.  Candidate validity is
the literal nonnegative center-plus-selected-neighbour inequality, not an
application contract.
-/

namespace CertificateClosedMarkedFan

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (marked : CertificateClosedMarkedFan ctx)

abbrev TypeBVertexReserve
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.CertificateClosedFanCandidate.VertexReserve ctx.G.Vertex

noncomputable def candidateProfile (reserve : TypeBVertexReserve ctx) :=
  Graph.CertificateClosedFanCandidate.Profile.selectionProfile
    marked.chargeProfile ctx.G.object.input.vertices.decEq marked.fan.center
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center) reserve

abbrev Candidate (reserve : TypeBVertexReserve ctx) :=
  (marked.candidateProfile reserve).Candidate

/-- Every selected item is a literal neighbour of the fan center. -/
theorem selected_adjacent (reserve : TypeBVertexReserve ctx)
    (candidate : marked.Candidate reserve)
    {port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center}
    (_selected : port ∈ candidate.1) :
    ctx.G.object.graph.Adj marked.fan.center
      (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) :=
  Graph.HighCenterPort.endpoint_adjacent ctx.G.object marked.fan.center port

/-- Deletion criticality derives, rather than assumes, that every selected
neighbour lies outside the high-center set `H_X`. -/
theorem selected_endpoint_cubic (reserve : TypeBVertexReserve ctx)
    (candidate : marked.Candidate reserve)
    {port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center}
    (_selected : port ∈ candidate.1) :
    ctx.G.object.degree
      (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) = 3 :=
  Graph.HighCenterPort.endpoint_cubic ctx.G.object marked.fan.center
    marked.centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) port

theorem selected_endpoint_not_high (reserve : TypeBVertexReserve ctx)
    (candidate : marked.Candidate reserve)
    {port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center}
    (selected : port ∈ candidate.1) :
    ¬4 ≤ ctx.G.object.degree
      (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) := by
  rw [marked.selected_endpoint_cubic reserve candidate selected]
  omega

/-- Candidate validity is exactly the manuscript's nonnegative augmented
center-plus-neighbour charge inequality, in quarter units. -/
theorem candidate_charge_nonnegative (reserve : TypeBVertexReserve ctx)
    (candidate : marked.Candidate reserve) :
    0 ≤
      Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge
          marked.chargeProfile +
        ∑ port ∈ candidate.1,
          marked.chargeProfile.quarterCharge port :=
  Graph.CertificateClosedFanCandidate.Profile.Candidate.charge_nonnegative
    marked.chargeProfile ctx.G.object.input.vertices.decEq marked.fan.center
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center) reserve
    candidate

theorem candidate_reserve_free (reserve : TypeBVertexReserve ctx)
    (candidate : marked.Candidate reserve)
    {port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center}
    (selected : port ∈ candidate.1) :
    ¬reserve.Used
      (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) :=
  Graph.CertificateClosedFanCandidate.Profile.Candidate.selected_reserve_free
    marked.chargeProfile ctx.G.object.input.vertices.decEq marked.fan.center
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center) reserve
    candidate selected

/-- Every declared vertex carrier is an actual neighbour of the marked fan
center (or the center itself). -/
theorem declaredCarrierSupport_reachable (reserve : TypeBVertexReserve ctx)
    {carrier : ctx.G.Vertex}
    (member : carrier ∈ (marked.candidateProfile reserve).declaredCarrierSupport) :
    ctx.G.object.graph.Reachable marked.fan.center carrier :=
  Graph.CertificateClosedFanCandidate.Profile.declaredCarrierSupport_reachable
    marked.chargeProfile ctx.G.object.input.vertices.decEq marked.fan.center
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center) reserve
    (fun port => Graph.HighCenterPort.endpoint_adjacent ctx.G.object
      marked.fan.center port) member

/-- The exact CT14 certificate-closed charge supplies the complete-neighbour
candidate whenever the ordinary reserve is locally free. -/
noncomputable def reserveFreeCandidate (reserve : TypeBVertexReserve ctx)
    (reserveFree : ∀ port,
      ¬reserve.Used
        (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port)) :
    marked.Candidate reserve :=
  Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate
    marked.chargeProfile ctx.G.object.input.vertices.decEq marked.fan.center
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center) reserve
    ctx.toBranchContext marked.charge_nonnegative reserveFree

end CertificateClosedMarkedFan

/-- Both Type B local branches now expose framework-defined concrete
candidate fibres. -/
structure VerifiedTypeBCandidateFibresPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedPositiveDeficitCandidatePrefix ctx
  certificateCandidateExists : ∀ (marked : CertificateClosedMarkedFan ctx)
    (reserve : CertificateClosedMarkedFan.TypeBVertexReserve ctx),
    (∀ port,
      ¬reserve.Used (Graph.HighCenterPort.endpoint ctx.G.object
        marked.fan.center port)) → Nonempty (marked.Candidate reserve)

noncomputable def verifiedTypeBCandidateFibresPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedPositiveDeficitCandidatePrefix ctx) :
    VerifiedTypeBCandidateFibresPrefix ctx where
  previous := previous
  certificateCandidateExists := fun marked reserve reserveFree =>
    ⟨marked.reserveFreeCandidate reserve reserveFree⟩

theorem exists_verifiedTypeBCandidateFibresPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBCandidateFibresPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedPositiveDeficitCandidatePrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBCandidateFibresPrefix ctx previous⟩

end Erdos64EG.Internal
