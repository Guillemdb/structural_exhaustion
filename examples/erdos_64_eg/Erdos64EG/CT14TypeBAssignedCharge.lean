import Erdos64EG.CT14TypeBChoiceLedger
import StructuralExhaustion.Graph.AssignedSupportCharge
import StructuralExhaustion.Graph.WindowExternalCharge

namespace Erdos64EG.Internal

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Exact assigned-support B-ledger

This stage instantiates the framework's graph-defined charge profile with the
literal counted core and the complete derived high-center set of a Type B
support.  Positive deficiency uses induced core degree, assigned surplus uses
ambient graph degree, and the B-ledger equation is inherited as a theorem.
-/

namespace TypeBLocalEntry

/-- Charged selected neighbours in the certificate branch. -/
noncomputable def certificateCoreSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (marked : CertificateClosedMarkedFan ctx)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      reserve).Candidate) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact candidate.1.image fun item =>
    Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center item.down

/-- Every fan-neighbour charge used by a positive entry. -/
noncomputable def positiveFanCoreSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : PositiveDeficitMarkedFan ctx) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (Graph.HighCenterPort.ports ctx.G.object
    entry.fan.center).orderedValues.toFinset.image fun port =>
      Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port

/-- Selected non-window remote endpoints in a positive entry. -/
noncomputable def positiveOrdinaryCoreSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate reserve.incidenceReserve) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  let profile := p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable
  exact (candidate.1.filter fun incidence =>
    Graph.HybridFanIncidence.incidenceKind
      (object := ctx.G.object) (center := entry.fan.center)
      profile incidence = .nonWindow).image fun incidence =>
        Graph.HybridFanIncidence.other
          (object := ctx.G.object) (center := entry.fan.center)
          profile incidence.1 incidence.2

noncomputable def positiveCombinedCoreSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate reserve.incidenceReserve) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact positiveFanCoreSupport entry ∪
    positiveOrdinaryCoreSupport reserve entry candidate

/-- Literal core vertices whose charges are consumed by one candidate. The
positive branch records every fan neighbour (because every one occurs in the
fan-charge sum) and only selected non-window remote endpoints. -/
noncomputable def actualCoreSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex) :
    (entry : TypeBLocalEntry ctx) →
      (entry.selectionProfile reserve).Candidate → Finset ctx.G.Vertex
  | .certificate marked, candidate => by
      exact certificateCoreSupport reserve marked candidate
  | .positive entry, candidate => by
      exact positiveCombinedCoreSupport reserve entry candidate

@[simp]
theorem actualCoreSupport_certificate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (marked : CertificateClosedMarkedFan ctx)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      reserve).Candidate) :
    (TypeBLocalEntry.certificate marked).actualCoreSupport reserve candidate =
      certificateCoreSupport reserve marked candidate := rfl

@[simp]
theorem actualCoreSupport_positive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate reserve.incidenceReserve) :
    (TypeBLocalEntry.positive entry).actualCoreSupport reserve candidate =
      positiveCombinedCoreSupport reserve entry candidate := rfl

end TypeBLocalEntry

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

theorem netQuarterCharge_eq_augmented_add_centers :
    support.assignedChargeProfile.netQuarterCharge =
      support.assignedChargeProfile.augmentedQuarterCharge +
        (support.centers.card : Int) :=
  support.assignedChargeProfile.netQuarterCharge_eq_augmented_add_centers

theorem reducedQuarterLedger_eq_netQuarterCharge :
    support.assignedChargeProfile.reducedQuarterLedger =
      support.assignedChargeProfile.netQuarterCharge :=
  support.assignedChargeProfile.reducedQuarterLedger_eq_netQuarterCharge

theorem netQuarterCharge_nonnegative_of_augmented
    (nonnegative :
      0 ≤ support.assignedChargeProfile.augmentedQuarterCharge) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge :=
  support.assignedChargeProfile.netQuarterCharge_nonnegative_of_augmented
    nonnegative

/-- In the certificate branch, the fixed local quarter balance is exactly the
assigned ambient-center entry of the global B-ledger. -/
theorem certificate_fixedQuarterBalance_eq_centerCharge
    (demand : support.Demand) (marked : CertificateClosedMarkedFan ctx)
    (entryEq : support.entry demand = .certificate marked) :
    (support.entry demand).fixedQuarterBalance =
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
        ctx.G.object demand.1 := by
  have centerEq : marked.fan.center = demand.1 := by
    have exactCenter := support.entry_center demand
    rw [entryEq] at exactCenter
    exact exactCenter
  have high := support.demand_high demand
  rw [entryEq]
  simp only [TypeBLocalEntry.fixedQuarterBalance]
  unfold Graph.CertificateClosedFanCandidate.Profile.centerQuarterCharge
  unfold Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
    Graph.AssignedSupportCharge.Profile.surplusAt
  have cardEq : marked.chargeProfile.members.card =
      ctx.G.object.degree marked.fan.center := by
    change (Graph.HighCenterPort.ports ctx.G.object marked.fan.center).card = _
    exact Graph.HighCenterPort.ports_card_eq_degree _ _
  rw [cardEq, centerEq]
  omega

/-- The finite candidate weight of a certificate neighbour is a safe lower
bound for that vertex's literal induced-core quarter charge.  The proof uses
the support API's automatic assignment of every internal core edge; extra
window/decorative assignments can only lower the candidate weight. -/
theorem certificate_portCharge_le_coreCharge
    (demand : support.Demand) (marked : CertificateClosedMarkedFan ctx)
    (entryEq : support.entry demand = .certificate marked)
    (port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center)
    (endpointMem :
      Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port ∈
        support.vertices) :
    marked.chargeProfile.quarterCharge port ≤
      support.assignedChargeProfile.coreQuarterChargeAt
        (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) := by
  have assignedInternal : ∀ other,
      ctx.G.object.graph.Adj
          (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port)
          other →
      other ∈ support.vertices → other ≠ marked.fan.center →
        marked.Assigned
          (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port,
            other) := by
    intro other adjacent otherMem _neCenter
    have assignedEntry : (support.entry demand).Assigned
        (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port,
          other) := by
      apply (support.entry_assigned demand _).2
      exact ⟨adjacent, Or.inr ⟨endpointMem, otherMem⟩⟩
    rw [entryEq] at assignedEntry
    exact assignedEntry
  have lower :=
    Graph.AssignedFanCharge.quarterCharge_le_inducedCoreQuarterCharge
      ctx.G.object marked.fan.center marked.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      marked.Assigned marked.assignedDecidable support.vertices port
      assignedInternal
  change marked.chargeProfile.quarterCharge port ≤ _
  simpa [markedFanChargeProfile, CertificateClosedMarkedFan.chargeProfile,
    Graph.AssignedSupportCharge.Profile.coreQuarterChargeAt,
    Graph.AssignedSupportCharge.Profile.positiveDeficiencyAt,
    Graph.AssignedSupportCharge.Profile.internalDegree,
    assignedChargeProfile] using lower

theorem certificateCandidate_endpoint_mem_vertices
    (marked : CertificateClosedMarkedFan ctx)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      support.reserve).Candidate)
    {item : ULift.{u, 0}
      (Graph.HighCenterPort.Port ctx.G.object marked.fan.center)}
    (selected : item ∈ candidate.1) :
    Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center item.down ∈
      support.vertices := by
  have free := TypeBLocalEntry.certificate_selected_vertex_reserve_free
    marked support.reserve candidate selected
  by_contra outside
  exact free (support.reserve_excludes_external outside)

theorem certificateCandidate_endpoint_not_center
    (marked : CertificateClosedMarkedFan ctx)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      support.reserve).Candidate)
    {item : ULift.{u, 0}
      (Graph.HighCenterPort.Port ctx.G.object marked.fan.center)}
    (selected : item ∈ candidate.1) :
    Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center item.down ∉
      support.centers := by
  have free := TypeBLocalEntry.certificate_selected_vertex_reserve_free
    marked support.reserve candidate selected
  intro center
  exact free (support.reserve_excludes_center center)

/-- A valid certificate candidate pays its assigned center with literal
induced-core vertex charges.  This is stronger than the abstract weighted
selection inequality: every selected lower-bound weight has been transferred
to an actual counted vertex of the support. -/
theorem certificateCandidate_actualBalance_nonnegative
    (demand : support.Demand) (marked : CertificateClosedMarkedFan ctx)
    (entryEq : support.entry demand = .certificate marked)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      support.reserve).Candidate) :
    0 ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ item ∈ candidate.1,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
              item.down) := by
  have localNonnegative :=
    TypeBLocalEntry.localQuarterBalance_nonnegative
      (TypeBLocalEntry.certificate marked) support.reserve candidate
  have fixedEq := support.certificate_fixedQuarterBalance_eq_centerCharge
    demand marked entryEq
  have sumLower :
      ∑ item ∈ candidate.1,
          ((TypeBLocalEntry.certificate marked).selectionProfile
            support.reserve).weight item ≤
        ∑ item ∈ candidate.1,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
              item.down) := by
    apply Finset.sum_le_sum
    intro item selected
    have endpointMem :=
      support.certificateCandidate_endpoint_mem_vertices marked candidate selected
    have portLower := support.certificate_portCharge_le_coreCharge
      demand marked entryEq item.down endpointMem
    simpa [TypeBLocalEntry.selectionProfile,
      Core.FiniteWeightedSelection.Profile.uliftItems,
      CertificateClosedMarkedFan.candidateProfile,
      Graph.CertificateClosedFanCandidate.Profile.selectionProfile] using portLower
  unfold TypeBLocalEntry.localQuarterBalance
    TypeBLocalEntry.selectedQuarterCredit at localNonnegative
  rw [entryEq] at fixedEq
  change TypeBLocalEntry.fixedQuarterBalance
      (TypeBLocalEntry.certificate marked) = _ at fixedEq
  omega

theorem certificateCandidate_localBalance_le_actualCharge
    (demand : support.Demand) (marked : CertificateClosedMarkedFan ctx)
    (entryEq : support.entry demand = .certificate marked)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      support.reserve).Candidate) :
    (TypeBLocalEntry.certificate marked).localQuarterBalance
        support.reserve candidate ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ item ∈ candidate.1,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
              item.down) := by
  have fixedEq := support.certificate_fixedQuarterBalance_eq_centerCharge
    demand marked entryEq
  rw [entryEq] at fixedEq
  have sumLower :
      ∑ item ∈ candidate.1,
          ((TypeBLocalEntry.certificate marked).selectionProfile
            support.reserve).weight item ≤
        ∑ item ∈ candidate.1,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
              item.down) := by
    apply Finset.sum_le_sum
    intro item selected
    have endpointMem :=
      support.certificateCandidate_endpoint_mem_vertices marked candidate selected
    have portLower := support.certificate_portCharge_le_coreCharge
      demand marked entryEq item.down endpointMem
    simpa [TypeBLocalEntry.selectionProfile,
      Core.FiniteWeightedSelection.Profile.uliftItems,
      CertificateClosedMarkedFan.candidateProfile,
      Graph.CertificateClosedFanCandidate.Profile.selectionProfile] using portLower
  unfold TypeBLocalEntry.localQuarterBalance
    TypeBLocalEntry.selectedQuarterCredit
  change TypeBLocalEntry.fixedQuarterBalance
      (TypeBLocalEntry.certificate marked) + _ ≤ _
  omega

namespace PositiveDeficit

def chargeProfile (entry : PositiveDeficitMarkedFan ctx) :=
  markedFanChargeProfile entry.fan entry.centerHigh entry.Assigned
    entry.assignedDecidable

end PositiveDeficit

/-- Core compatibility makes the port-level assigned-closure count exactly
the CT14 cubic-closed-neighbour count used in the positive deficit. -/
theorem positive_closedCount_eq_cubicClosedCount
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry) :
    (PositiveDeficit.chargeProfile entry).closedCount ctx.toBranchContext =
      (Graph.HybridFanIncidence.closedMembers
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable)).card := by
  have coreCompatible := support.localEntry_coreCompatible demand
  rw [entryEq] at coreCompatible
  have allRemainder : ∀ port : Graph.HighCenterPort.Port ctx.G.object
      entry.fan.center,
      (p13FanWindowProfile ctx entry.Assigned
        entry.assignedDecidable).RemainderSide
          (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) := by
    intro port
    exact support.vertices_remainder (coreCompatible port)
  rw [(PositiveDeficit.chargeProfile entry).closedCount_eq_closedMembers_card
    ctx.toBranchContext]
  calc
    (PositiveDeficit.chargeProfile entry).closedMembers.card =
        (Graph.FanClosedPortMass.assignedClosedPorts
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card := by
      rfl
    _ = (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card := by
      symm
      exact Graph.FanClosedPortMass.cubicClosed_card_eq_assignedClosedPorts_card
        entry.centerHigh
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx))
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        allRemainder

/-- Before incidence credits are transferred, the actual assigned fan
weights plus the center are bounded below by the negative of the exact CT14
deficit. -/
theorem positive_assignedFanCharge_ge_negativeDeficit
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry) :
    -Graph.FanClosedPortMass.deficitNumerator
        (ctx.G.object.degree entry.fan.center)
        (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
          entry.fan.center).orderedValues.toFinset,
          (PositiveDeficit.chargeProfile entry).quarterCharge port := by
  let emptyReserve :
      Graph.CertificateClosedFanCandidate.VertexReserve ctx.G.Vertex := {
    Used := fun _vertex => False
    usedDecidable := fun _vertex => isFalse (fun impossible => impossible)
  }
  have weightLower :=
    Graph.CertificateClosedFanCandidate.Profile.allItems_weight_ge
      (PositiveDeficit.chargeProfile entry)
      ctx.G.object.input.vertices.decEq entry.fan.center
      (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center)
      emptyReserve ctx.toBranchContext
  change
    -((PositiveDeficit.chargeProfile entry).closedCount
        ctx.toBranchContext : Int) +
        3 * ((PositiveDeficit.chargeProfile entry).openCount
          ctx.toBranchContext : Int) ≤
      ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
        entry.fan.center).orderedValues.toFinset,
          (PositiveDeficit.chargeProfile entry).quarterCharge port at weightLower
  have closedEq := support.positive_closedCount_eq_cubicClosedCount
    demand entry entryEq
  have partition :=
    (PositiveDeficit.chargeProfile entry).count_partition ctx.toBranchContext
  have cardEq : (PositiveDeficit.chargeProfile entry).members.card =
      ctx.G.object.degree entry.fan.center :=
    Graph.HighCenterPort.ports_card_eq_degree _ _
  have centerEq : entry.fan.center = demand.1 := by
    have exactCenter := support.entry_center demand
    rw [entryEq] at exactCenter
    exact exactCenter
  rw [← closedEq]
  unfold Graph.FanClosedPortMass.deficitNumerator
  unfold Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
    Graph.AssignedSupportCharge.Profile.surplusAt
  have partition' := partition
  rw [cardEq] at partition'
  have centerHigh : 4 ≤ ctx.G.object.degree entry.fan.center :=
    entry.centerHigh
  rw [← centerEq]
  omega

/-- The abstract window multiplicity is not free credit: every one of its
literal incidences is an assigned shoulder outside the remainder-side counted
core, so the induced-core correction pays it. -/
theorem positive_windowQuarterCredit_le_externalCorrection
    (entry : PositiveDeficitMarkedFan ctx) :
    (Graph.HybridFanIncidence.windowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) ≤
      4 * (∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
        entry.fan.center).orderedValues.toFinset,
          Graph.AssignedFanCharge.externalAssignedShoulderCount ctx.G.object
            entry.fan.center entry.centerHigh
            ((fixedPackedInput ctx).dart_has_tight_endpoint
              (packedStaticInput.fixedContext ctx))
            entry.Assigned entry.assignedDecidable support.vertices port : Nat) := by
  apply Graph.WindowExternalCharge.windowQuarterCredit_le_externalCorrection
    (base := fixedPackedInput ctx) (object := ctx.G.object)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (center := entry.fan.center) entry.centerHigh
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
    support.vertices
  intro vertex member
  exact support.vertices_remainder member

/-- At every positive-fan port, the assigned local weight together with all
external assigned-shoulder corrections is bounded by the literal induced-core
charge of that actual endpoint. -/
theorem positive_portCharge_add_externalCorrection_le_coreCharge
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry)
    (port : Graph.HighCenterPort.Port ctx.G.object entry.fan.center) :
    (PositiveDeficit.chargeProfile entry).quarterCharge port +
        4 * (Graph.AssignedFanCharge.externalAssignedShoulderCount ctx.G.object
          entry.fan.center entry.centerHigh
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx))
          entry.Assigned entry.assignedDecidable support.vertices port : Int) ≤
      support.assignedChargeProfile.coreQuarterChargeAt
        (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) := by
  have coreCompatible := support.localEntry_coreCompatible demand
  rw [entryEq] at coreCompatible
  have endpointMem := coreCompatible port
  have centerEq : entry.fan.center = demand.1 := by
    have exactCenter := support.entry_center demand
    rw [entryEq] at exactCenter
    exact exactCenter
  have centerMem : entry.fan.center ∈ support.vertices := by
    rw [centerEq]
    exact support.demand_mem_vertices demand
  have internalAssigned : ∀ other,
      ctx.G.object.graph.Adj
          (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port)
          other →
      other ∈ support.vertices → other ≠ entry.fan.center →
        entry.Assigned
          (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port,
            other) := by
    intro other adjacent otherMem _neCenter
    have assignedEntry : (support.entry demand).Assigned
        (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port,
          other) := by
      apply (support.entry_assigned demand _).2
      exact ⟨adjacent, Or.inr ⟨endpointMem, otherMem⟩⟩
    rw [entryEq] at assignedEntry
    exact assignedEntry
  have lower :=
    Graph.AssignedFanCharge.quarterCharge_add_externalCorrection_le_inducedCoreQuarterCharge
      ctx.G.object entry.fan.center entry.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      entry.Assigned entry.assignedDecidable support.vertices centerMem port
      internalAssigned
  simpa [PositiveDeficit.chargeProfile, markedFanChargeProfile,
    assignedChargeProfile,
    Graph.AssignedSupportCharge.Profile.coreQuarterChargeAt,
    Graph.AssignedSupportCharge.Profile.positiveDeficiencyAt,
    Graph.AssignedSupportCharge.Profile.internalDegree] using lower

/-- Summing the pointwise correction theorem shows that actual induced-core
charges of the complete fan pay both the assigned fan weights and the exact
window multiplicity credit. -/
theorem positive_assignedFan_add_window_le_fanCoreCharge
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry) :
    (∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
        entry.fan.center).orderedValues.toFinset,
          (PositiveDeficit.chargeProfile entry).quarterCharge port) +
      (Graph.HybridFanIncidence.windowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) ≤
      ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
        entry.fan.center).orderedValues.toFinset,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) := by
  let ports := (Graph.HighCenterPort.ports ctx.G.object
    entry.fan.center).orderedValues.toFinset
  let external := fun port : Graph.HighCenterPort.Port ctx.G.object
      entry.fan.center =>
    Graph.AssignedFanCharge.externalAssignedShoulderCount ctx.G.object
      entry.fan.center entry.centerHigh
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))
      entry.Assigned entry.assignedDecidable support.vertices port
  change
    (∑ port ∈ ports,
      (PositiveDeficit.chargeProfile entry).quarterCharge port) +
      (Graph.HybridFanIncidence.windowQuarterCredit
        (base := fixedPackedInput ctx) (object := ctx.G.object)
        (baseline := (packedStaticInput.fixedContext ctx).baseline)
        (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned
          entry.assignedDecidable) : Int) ≤
      ∑ port ∈ ports,
        support.assignedChargeProfile.coreQuarterChargeAt
          (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port)
  apply Graph.WindowExternalCharge.sum_weight_add_credit_le_actual
    ports
    (fun port => (PositiveDeficit.chargeProfile entry).quarterCharge port)
    (fun port => support.assignedChargeProfile.coreQuarterChargeAt
      (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port))
    external
  · have windowLower :=
      support.positive_windowQuarterCredit_le_externalCorrection entry
    change _ ≤ (4 : Int) * ↑(∑ port ∈ ports, external port)
      at windowLower
    exact windowLower
  · intro port _member
    exact support.positive_portCharge_add_externalCorrection_le_coreCharge
      demand entry entryEq port

/-- The positive branch's fixed B1 term is now a theorem about actual graph
charge.  No incidence multiplicity or deficit is accepted as a free balance. -/
theorem positive_fixedQuarterBalance_le_actualFanBalance
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry) :
    (TypeBLocalEntry.positive entry).fixedQuarterBalance ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
          entry.fan.center).orderedValues.toFinset,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) := by
  have deficitLower := support.positive_assignedFanCharge_ge_negativeDeficit
    demand entry entryEq
  have fanTransfer := support.positive_assignedFan_add_window_le_fanCoreCharge
    demand entry entryEq
  change
    (Graph.HybridFanIncidence.windowQuarterCredit
      (base := fixedPackedInput ctx) (object := ctx.G.object)
      (baseline := (packedStaticInput.fixedContext ctx).baseline)
      (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned
        entry.assignedDecidable) : Int) -
      Graph.FanClosedPortMass.deficitNumerator
        (ctx.G.object.degree entry.fan.center)
        (Graph.HybridFanIncidence.closedMembers
          (object := ctx.G.object) (center := entry.fan.center)
          (p13FanWindowProfile ctx entry.Assigned
            entry.assignedDecidable)).card ≤ _
  omega

/-- A selected non-window incidence is backed by an ordinary literal core
vertex. This follows from the canonical framework reserve and is not a field
of the positive fan entry or assigned support. -/
theorem positiveCandidate_nonWindow_ordinary
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate support.reserve.incidenceReserve)
    {incidence : Graph.HybridFanIncidence.Incidence
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)}
    (selected : incidence ∈ candidate.1)
    (nonWindow : Graph.HybridFanIncidence.incidenceKind
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      incidence = .nonWindow) :
    Graph.InducedCoreFanReserve.OrdinaryAvailable ctx.G.object
      support.assignedChargeProfile
      (Graph.HybridFanIncidence.other
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence.1 incidence.2) := by
  have free := entry.candidate_reserve_free support.reserve.incidenceReserve
    candidate selected
  have notCovered :
      Graph.HybridFanIncidence.other
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence.1 incidence.2 ∉ p13CoveredVertices ctx := by
    have notWindow :=
      (Graph.HybridFanIncidence.incidenceKind_eq_nonWindow_iff
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
        incidence).1 nonWindow
    exact notWindow
  apply support.reserve_free_nonWindow_ordinary
    (carrier := Graph.HybridFanIncidence.carrier
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      incidence)
  · exact free
  · exact notCovered

theorem positiveCandidate_selectedCredit_le_actualOrdinaryCharge
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate support.reserve.incidenceReserve) :
    (∑ incidence ∈ candidate.1,
        if Graph.HybridFanIncidence.incidenceKind
            (object := ctx.G.object) (center := entry.fan.center)
            (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
            incidence = .nonWindow then (2 : Int) else 0) ≤
      (∑ incidence ∈ candidate.1,
        if Graph.HybridFanIncidence.incidenceKind
            (object := ctx.G.object) (center := entry.fan.center)
            (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
            incidence = .nonWindow then
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HybridFanIncidence.other
              (object := ctx.G.object) (center := entry.fan.center)
              (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
              incidence.1 incidence.2)
        else 0) := by
  apply Finset.sum_le_sum
  intro incidence selected
  by_cases nonWindow : Graph.HybridFanIncidence.incidenceKind
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      incidence = .nonWindow
  · simp only [nonWindow, if_true]
    exact (support.positiveCandidate_nonWindow_ordinary entry candidate
      selected nonWindow).2.2.2
  · simp only [nonWindow, if_false]
    exact le_rfl

/-- Every valid positive candidate's abstract B1 balance is bounded by a sum
of literal, pairwise named induced-core charges. -/
theorem positiveCandidate_localBalance_le_actualCharge
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry)
    (candidate : entry.Candidate support.reserve.incidenceReserve) :
    ((TypeBLocalEntry.positive entry).fixedQuarterBalance +
        ∑ incidence ∈ candidate.1,
          if Graph.HybridFanIncidence.incidenceKind
              (object := ctx.G.object) (center := entry.fan.center)
              (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
              incidence = .nonWindow then (2 : Int) else 0) ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
          entry.fan.center).orderedValues.toFinset,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) +
        ∑ incidence ∈ candidate.1,
          if Graph.HybridFanIncidence.incidenceKind
              (object := ctx.G.object) (center := entry.fan.center)
              (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
              incidence = .nonWindow then
            support.assignedChargeProfile.coreQuarterChargeAt
              (Graph.HybridFanIncidence.other
                (object := ctx.G.object) (center := entry.fan.center)
                (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
                incidence.1 incidence.2)
          else 0 := by
  have fixed := support.positive_fixedQuarterBalance_le_actualFanBalance
    demand entry entryEq
  have selected :=
    support.positiveCandidate_selectedCredit_le_actualOrdinaryCharge
      entry candidate
  omega

theorem certificate_actualCoreSupport_charge
    (marked : CertificateClosedMarkedFan ctx)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      support.reserve).Candidate) :
    ∑ vertex ∈ (TypeBLocalEntry.certificate marked).actualCoreSupport
        support.reserve candidate,
        support.assignedChargeProfile.coreQuarterChargeAt vertex =
      ∑ item ∈ candidate.1,
        support.assignedChargeProfile.coreQuarterChargeAt
          (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center
            item.down) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [TypeBLocalEntry.actualCoreSupport_certificate]
  unfold TypeBLocalEntry.certificateCoreSupport
  rw [Finset.sum_image]
  intro left _leftMem right _rightMem equal
  apply ULift.ext
  exact Graph.HighCenterPort.endpoint_injective ctx.G.object
    marked.fan.center equal

theorem positive_fanVertices_charge
    (entry : PositiveDeficitMarkedFan ctx) :
    ∑ vertex ∈ TypeBLocalEntry.positiveFanCoreSupport entry,
        support.assignedChargeProfile.coreQuarterChargeAt vertex =
      ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
        entry.fan.center).orderedValues.toFinset,
        support.assignedChargeProfile.coreQuarterChargeAt
          (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold TypeBLocalEntry.positiveFanCoreSupport
  rw [Finset.sum_image]
  intro left _leftMem right _rightMem equal
  exact Graph.HighCenterPort.endpoint_injective ctx.G.object
    entry.fan.center equal

theorem positive_ordinaryVertices_charge
    (entry : PositiveDeficitMarkedFan ctx)
    (candidate : entry.Candidate support.reserve.incidenceReserve) :
    ∑ vertex ∈ TypeBLocalEntry.positiveOrdinaryCoreSupport
        support.reserve entry candidate,
        support.assignedChargeProfile.coreQuarterChargeAt vertex =
      ∑ incidence ∈ candidate.1,
        if Graph.HybridFanIncidence.incidenceKind
            (object := ctx.G.object) (center := entry.fan.center)
            (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
            incidence = .nonWindow then
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HybridFanIncidence.other
              (object := ctx.G.object) (center := entry.fan.center)
              (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
              incidence.1 incidence.2)
        else 0 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold TypeBLocalEntry.positiveOrdinaryCoreSupport
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro left _leftMem right _rightMem equal
    exact (Graph.HybridFanIncidence.other_injective
      (object := ctx.G.object) (center := entry.fan.center)
      (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
      (fourCycleFree ctx)) equal

theorem positive_fanVertices_disjoint_ordinaryVertices
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry)
    (candidate : entry.Candidate support.reserve.incidenceReserve) :
    Disjoint
      (TypeBLocalEntry.positiveFanCoreSupport entry)
      (TypeBLocalEntry.positiveOrdinaryCoreSupport
        support.reserve entry candidate) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold TypeBLocalEntry.positiveFanCoreSupport
    TypeBLocalEntry.positiveOrdinaryCoreSupport
  rw [Finset.disjoint_left]
  intro vertex fanMem ordinaryMem
  rcases Finset.mem_image.mp fanMem with ⟨port, _portMem, rfl⟩
  rcases Finset.mem_image.mp ordinaryMem with
    ⟨incidence, incidenceMem, equal⟩
  have selected := (Finset.mem_filter.mp incidenceMem).1
  have nonWindow := (Finset.mem_filter.mp incidenceMem).2
  have ordinary := support.positiveCandidate_nonWindow_ordinary
    entry candidate selected nonWindow
  have centerEq : entry.fan.center = demand.1 := by
    have exactCenter := support.entry_center demand
    rw [entryEq] at exactCenter
    exact exactCenter
  have centerMem : entry.fan.center ∈ support.centers := by
    rw [centerEq]
    exact demand.2
  have notAdjacent := ordinary.2.2.1 entry.fan.center centerMem
  apply notAdjacent
  rw [equal]
  exact Graph.HighCenterPort.endpoint_adjacent ctx.G.object
    entry.fan.center port

theorem positive_actualCoreSupport_charge
    (demand : support.Demand) (entry : PositiveDeficitMarkedFan ctx)
    (entryEq : support.entry demand = .positive entry)
    (candidate : entry.Candidate support.reserve.incidenceReserve) :
    ∑ vertex ∈ (TypeBLocalEntry.positive entry).actualCoreSupport
        support.reserve candidate,
        support.assignedChargeProfile.coreQuarterChargeAt vertex =
      (∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
          entry.fan.center).orderedValues.toFinset,
          support.assignedChargeProfile.coreQuarterChargeAt
            (Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port)) +
        ∑ incidence ∈ candidate.1,
          if Graph.HybridFanIncidence.incidenceKind
              (object := ctx.G.object) (center := entry.fan.center)
              (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
              incidence = .nonWindow then
            support.assignedChargeProfile.coreQuarterChargeAt
              (Graph.HybridFanIncidence.other
                (object := ctx.G.object) (center := entry.fan.center)
                (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)
                incidence.1 incidence.2)
          else 0 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [TypeBLocalEntry.actualCoreSupport_positive]
  unfold TypeBLocalEntry.positiveCombinedCoreSupport
  rw [Finset.sum_union
    (support.positive_fanVertices_disjoint_ordinaryVertices
      demand entry entryEq candidate)]
  rw [support.positive_fanVertices_charge entry,
    support.positive_ordinaryVertices_charge entry candidate]

/-- Branch-independent literal transfer for one candidate. -/
theorem localQuarterBalance_le_actualCoreSupport
    (demand : support.Demand)
    (candidate : ((support.entry demand).selectionProfile
      support.reserve).Candidate) :
    (support.entry demand).localQuarterBalance support.reserve candidate ≤
      Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1 +
        ∑ vertex ∈ (support.entry demand).actualCoreSupport
          support.reserve candidate,
          support.assignedChargeProfile.coreQuarterChargeAt vertex := by
  revert candidate
  cases entryEq : support.entry demand with
  | certificate marked =>
      intro candidate
      have actual := support.certificateCandidate_localBalance_le_actualCharge
        demand marked entryEq candidate
      have sumEq := support.certificate_actualCoreSupport_charge marked candidate
      rw [sumEq]
      simpa [add_assoc] using actual
  | positive entry =>
      intro candidate
      have actual := support.positiveCandidate_localBalance_le_actualCharge
        demand entry entryEq candidate
      have sumEq := support.positive_actualCoreSupport_charge
        demand entry entryEq candidate
      unfold TypeBLocalEntry.localQuarterBalance
        TypeBLocalEntry.selectedQuarterCredit
      change
        ((TypeBLocalEntry.positive entry).fixedQuarterBalance +
            ∑ incidence ∈ candidate.1,
              if Graph.HybridFanIncidence.incidenceKind
                  (object := ctx.G.object) (center := entry.fan.center)
                  (p13FanWindowProfile ctx entry.Assigned
                    entry.assignedDecidable) incidence = .nonWindow then
                (2 : Int) else 0) ≤
          Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
              ctx.G.object demand.1 +
            ∑ vertex ∈ (TypeBLocalEntry.positive entry).actualCoreSupport
              support.reserve candidate,
              support.assignedChargeProfile.coreQuarterChargeAt vertex
      calc
        _ ≤ (Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
              ctx.G.object demand.1 +
            ∑ port ∈ (Graph.HighCenterPort.ports ctx.G.object
              entry.fan.center).orderedValues.toFinset,
              support.assignedChargeProfile.coreQuarterChargeAt
                (Graph.HighCenterPort.endpoint ctx.G.object
                  entry.fan.center port)) +
            ∑ incidence ∈ candidate.1,
              if Graph.HybridFanIncidence.incidenceKind
                  (object := ctx.G.object) (center := entry.fan.center)
                  (p13FanWindowProfile ctx entry.Assigned
                    entry.assignedDecidable) incidence = .nonWindow then
                support.assignedChargeProfile.coreQuarterChargeAt
                  (Graph.HybridFanIncidence.other
                    (object := ctx.G.object) (center := entry.fan.center)
                    (p13FanWindowProfile ctx entry.Assigned
                      entry.assignedDecidable) incidence.1 incidence.2)
              else 0 := actual
        _ = _ := by
          rw [sumEq]
          exact add_assoc _ _ _

/-- Every literal core charge consumed by a local balance is carried by the
same concrete candidate.  Consequently the framework's carrier-disjoint
choice cannot reuse any charged core vertex. -/
theorem actualCoreSupport_subset_carrierSupport
    (demand : support.Demand)
    (candidate : ((support.entry demand).selectionProfile
      support.reserve).Candidate) :
    (support.entry demand).actualCoreSupport support.reserve candidate ⊆
      (support.selectionProfile demand).carrierSupport candidate := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  change
    (support.entry demand).actualCoreSupport support.reserve candidate ⊆
      ((support.entry demand).selectionProfile support.reserve).carrierSupport
        candidate
  revert candidate
  cases entryEq : support.entry demand with
  | certificate marked =>
      intro candidate vertex member
      rw [TypeBLocalEntry.actualCoreSupport_certificate] at member
      unfold TypeBLocalEntry.certificateCoreSupport at member
      rcases Finset.mem_image.mp member with
        ⟨item, selected, rfl⟩
      apply Core.FiniteWeightedSelection.Profile.itemSupport_subset
        ((TypeBLocalEntry.certificate marked).selectionProfile
          support.reserve) candidate selected
      simp [TypeBLocalEntry.selectionProfile,
        Core.FiniteWeightedSelection.Profile.uliftItems,
        CertificateClosedMarkedFan.candidateProfile,
        Graph.CertificateClosedFanCandidate.Profile.selectionProfile]
  | positive entry =>
      intro candidate vertex member
      rw [TypeBLocalEntry.actualCoreSupport_positive] at member
      unfold TypeBLocalEntry.positiveCombinedCoreSupport at member
      rcases Finset.mem_union.mp member with fanMember | ordinaryMember
      · unfold TypeBLocalEntry.positiveFanCoreSupport at fanMember
        rcases Finset.mem_image.mp fanMember with
          ⟨port, _portMember, rfl⟩
        apply Core.FiniteWeightedSelection.Profile.baseSupport_subset
          ((TypeBLocalEntry.positive entry).selectionProfile
            support.reserve) candidate
        simp [TypeBLocalEntry.selectionProfile,
          PositiveDeficitMarkedFan.candidateProfile,
          Graph.HybridFanCandidate.profile,
          Graph.HybridFanCandidate.baseSupport]
      · unfold TypeBLocalEntry.positiveOrdinaryCoreSupport at ordinaryMember
        rcases Finset.mem_image.mp ordinaryMember with
          ⟨incidence, filtered, rfl⟩
        have selected := (Finset.mem_filter.mp filtered).1
        apply Core.FiniteWeightedSelection.Profile.itemSupport_subset
          ((TypeBLocalEntry.positive entry).selectionProfile
            support.reserve) candidate selected
        simp [TypeBLocalEntry.selectionProfile,
          PositiveDeficitMarkedFan.candidateProfile,
          Graph.HybridFanCandidate.profile,
          Graph.HybridFanCandidate.incidenceSupport]

/-- Every vertex whose core charge is consumed by a local entry is a literal
member of the counted induced core. -/
theorem actualCoreSupport_subset_core
    (demand : support.Demand)
    (candidate : ((support.entry demand).selectionProfile
      support.reserve).Candidate) :
    (support.entry demand).actualCoreSupport support.reserve candidate ⊆
      support.vertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  revert candidate
  cases entryEq : support.entry demand with
  | certificate marked =>
      intro candidate vertex member
      rw [TypeBLocalEntry.actualCoreSupport_certificate] at member
      unfold TypeBLocalEntry.certificateCoreSupport at member
      rcases Finset.mem_image.mp member with
        ⟨item, selected, rfl⟩
      exact support.certificateCandidate_endpoint_mem_vertices
        marked candidate selected
  | positive entry =>
      intro candidate vertex member
      rw [TypeBLocalEntry.actualCoreSupport_positive] at member
      unfold TypeBLocalEntry.positiveCombinedCoreSupport at member
      rcases Finset.mem_union.mp member with fanMember | ordinaryMember
      · unfold TypeBLocalEntry.positiveFanCoreSupport at fanMember
        rcases Finset.mem_image.mp fanMember with
          ⟨port, _portMember, rfl⟩
        have compatible := support.localEntry_coreCompatible demand
        rw [entryEq] at compatible
        exact compatible port
      · unfold TypeBLocalEntry.positiveOrdinaryCoreSupport at ordinaryMember
        rcases Finset.mem_image.mp ordinaryMember with
          ⟨incidence, filtered, rfl⟩
        exact (support.positiveCandidate_nonWindow_ordinary entry candidate
          (Finset.mem_filter.mp filtered).1
          (Finset.mem_filter.mp filtered).2).1

/-- Local entries never consume the ordinary core charge of an assigned high
center.  Those center-core charges are retained for the exact `+|H|`
correction in the reduced B-ledger. -/
theorem actualCoreSupport_disjoint_centers
    (demand : support.Demand)
    (candidate : ((support.entry demand).selectionProfile
      support.reserve).Candidate) :
    Disjoint
      ((support.entry demand).actualCoreSupport support.reserve candidate)
      support.centers := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [Finset.disjoint_left]
  revert candidate
  cases entryEq : support.entry demand with
  | certificate marked =>
      intro candidate vertex member centerMember
      rw [TypeBLocalEntry.actualCoreSupport_certificate] at member
      unfold TypeBLocalEntry.certificateCoreSupport at member
      rcases Finset.mem_image.mp member with
        ⟨item, selected, rfl⟩
      exact support.certificateCandidate_endpoint_not_center
        marked candidate selected centerMember
  | positive entry =>
      intro candidate vertex member centerMember
      rw [TypeBLocalEntry.actualCoreSupport_positive] at member
      unfold TypeBLocalEntry.positiveCombinedCoreSupport at member
      rcases Finset.mem_union.mp member with fanMember | ordinaryMember
      · unfold TypeBLocalEntry.positiveFanCoreSupport at fanMember
        rcases Finset.mem_image.mp fanMember with
          ⟨port, _portMember, rfl⟩
        have cubic := Graph.HighCenterPort.endpoint_cubic ctx.G.object
          entry.fan.center entry.centerHigh
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) port
        have high := support.demand_high
          ⟨Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port,
            centerMember⟩
        rw [cubic] at high
        omega
      · unfold TypeBLocalEntry.positiveOrdinaryCoreSupport at ordinaryMember
        rcases Finset.mem_image.mp ordinaryMember with
          ⟨incidence, filtered, rfl⟩
        exact (support.positiveCandidate_nonWindow_ordinary entry candidate
          (Finset.mem_filter.mp filtered).1
          (Finset.mem_filter.mp filtered).2).2.1 centerMember

/-- The complete demand set, exposed as a finset for exact disjoint-union
summation. -/
noncomputable def fullDemandSet : Finset support.Demand :=
  by
    letI : DecidableEq support.Demand := support.demands.decEq
    exact support.demands.orderedValues.toFinset

@[simp]
theorem mem_fullDemandSet (demand : support.Demand) :
    demand ∈ support.fullDemandSet := by
  letI : DecidableEq support.Demand := support.demands.decEq
  simp [fullDemandSet]

/-- The local candidate selected at a demand by a full CT12 choice. -/
noncomputable def fullChosenLocalCandidate
    (choice : support.completionProfile.FullChoice)
    (demand : support.Demand) :
    ((support.entry demand).selectionProfile support.reserve).Candidate := by
  change support.Candidate demand
  exact choice.entry ⟨demand, FinEnum.mem_orderedValues support.demands demand⟩

/-- Literal charged core support consumed at one demand of a full choice. -/
noncomputable def fullActualCoreSupport
    (choice : support.completionProfile.FullChoice)
    (demand : support.Demand) : Finset ctx.G.Vertex :=
  (support.entry demand).actualCoreSupport support.reserve
    (support.fullChosenLocalCandidate choice demand)

/-- Full-choice actual supports are pairwise disjoint.  The proof is the
framework's refined-support transport applied to the literal subset theorem
above. -/
theorem fullActualCoreSupport_disjoint
    (choice : support.completionProfile.FullChoice)
    (left right : support.Demand) (distinct : left ≠ right) :
    Disjoint (support.fullActualCoreSupport choice left)
      (support.fullActualCoreSupport choice right) := by
  let leftScheduled : {demand //
      demand ∈ support.completionProfile.fullSchedule} :=
    ⟨left, FinEnum.mem_orderedValues support.demands left⟩
  let rightScheduled : {demand //
      demand ∈ support.completionProfile.fullSchedule} :=
    ⟨right, FinEnum.mem_orderedValues support.demands right⟩
  have separated :=
    Core.FiniteRefinedLedger.Profile.Choice.refinedSupport_pairwiseDisjoint
      support.completionProfile choice
      (fun demand candidate =>
        (support.entry demand).actualCoreSupport support.reserve candidate)
      (fun demand candidate =>
        support.actualCoreSupport_subset_carrierSupport demand candidate)
      leftScheduled rightScheduled (by
        simpa [leftScheduled, rightScheduled] using distinct)
  simpa [fullActualCoreSupport, fullChosenLocalCandidate,
    leftScheduled, rightScheduled] using separated

theorem fullActualCoreSupport_pairwiseDisjoint
    (choice : support.completionProfile.FullChoice) :
    Set.PairwiseDisjoint (↑support.fullDemandSet)
      (support.fullActualCoreSupport choice) := by
  intro left _leftMember right _rightMember distinct
  exact support.fullActualCoreSupport_disjoint choice left right distinct

/-- The exact union of core vertices whose charges are consumed by a full
choice. -/
noncomputable def usedCore
    (choice : support.completionProfile.FullChoice) : Finset ctx.G.Vertex := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact support.fullDemandSet.biUnion (support.fullActualCoreSupport choice)

/-- Pairwise carrier disjointness turns the sum over the used core into the
sum of the per-demand literal core-charge sums, with equality rather than an
upper bound. -/
theorem usedCore_charge_eq_sum
    (choice : support.completionProfile.FullChoice) :
    (∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex) =
      ∑ demand ∈ support.fullDemandSet,
        ∑ vertex ∈ support.fullActualCoreSupport choice demand,
          support.assignedChargeProfile.coreQuarterChargeAt vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold usedCore
  exact Finset.sum_biUnion
    (f := support.assignedChargeProfile.coreQuarterChargeAt)
    (support.fullActualCoreSupport_pairwiseDisjoint choice)

theorem usedCore_subset_core
    (choice : support.completionProfile.FullChoice) :
    support.usedCore choice ⊆ support.vertices := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  intro vertex member
  unfold usedCore at member
  rcases Finset.mem_biUnion.mp member with
    ⟨demand, _demandMember, actualMember⟩
  exact support.actualCoreSupport_subset_core demand
    (support.fullChosenLocalCandidate choice demand) actualMember

theorem usedCore_disjoint_centers
    (choice : support.completionProfile.FullChoice) :
    Disjoint (support.usedCore choice) support.centers := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [Finset.disjoint_left]
  intro vertex member centerMember
  unfold usedCore at member
  rcases Finset.mem_biUnion.mp member with
    ⟨demand, _demandMember, actualMember⟩
  exact (Finset.disjoint_left.mp
    (support.actualCoreSupport_disjoint_centers demand
      (support.fullChosenLocalCandidate choice demand)))
      actualMember centerMember

noncomputable def processedCore
    (choice : support.completionProfile.FullChoice) : Finset ctx.G.Vertex :=
  support.assignedChargeProfile.processedCore (support.usedCore choice)

noncomputable def remainingCore
    (choice : support.completionProfile.FullChoice) : Finset ctx.G.Vertex :=
  support.assignedChargeProfile.remainingCore (support.usedCore choice)

theorem centers_subset_core : support.centers ⊆ support.vertices := by
  intro center member
  exact support.demand_mem_vertices ⟨center, member⟩

theorem processedCore_subset_core
    (choice : support.completionProfile.FullChoice) :
    support.processedCore choice ⊆ support.vertices := by
  exact support.assignedChargeProfile.processedCore_subset_core
    (support.usedCore choice) (support.usedCore_subset_core choice)
      support.centers_subset_core

/-- Exact core-charge partition into selected local resources, retained
high-center core charges, and the still-unprocessed ordinary remainder. -/
theorem coreQuarterCharge_eq_used_add_centers_add_remaining
    (choice : support.completionProfile.FullChoice) :
    support.assignedChargeProfile.coreQuarterCharge =
      (∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex) +
      (∑ center ∈ support.centers,
        support.assignedChargeProfile.coreQuarterChargeAt center) +
      ∑ vertex ∈ support.remainingCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex := by
  exact Graph.AssignedSupportCharge.Profile.coreQuarterCharge_eq_used_add_centers_add_remaining
      support.assignedChargeProfile (support.usedCore choice)
      (support.usedCore_subset_core choice) support.centers_subset_core
      (support.usedCore_disjoint_centers choice)

/-- The full demand sum is exactly the assigned-center term in the graph
ledger; the demand subtype contains every and only assigned center. -/
theorem fullCenterCharge_eq_centerQuarterCharge :
    (∑ demand ∈ support.fullDemandSet,
        Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1) =
      support.assignedChargeProfile.centerQuarterCharge := by
  letI : DecidableEq support.Demand := support.demands.decEq
  letI : FinEnum support.Demand := support.demands
  have all : support.fullDemandSet = Finset.univ := by
    ext demand
    simp
  rw [all]
  unfold Graph.AssignedSupportCharge.Profile.centerQuarterCharge
    assignedChargeProfile
  exact Finset.sum_coe_sort support.centers
    (Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt ctx.G.object)

noncomputable def remainingQuarterCharge
    (choice : support.completionProfile.FullChoice) : Int :=
  ∑ vertex ∈ support.remainingCore choice,
    support.assignedChargeProfile.coreQuarterChargeAt vertex

/-- The retained core charge of every assigned high center, together with its
one-unit reduced-ledger correction, is nonnegative pointwise. -/
theorem centerCoreCharge_add_card_nonnegative :
    0 ≤
      (∑ center ∈ support.centers,
        support.assignedChargeProfile.coreQuarterChargeAt center) +
      (support.centers.card : Int) :=
  support.assignedChargeProfile.centerCoreCharge_add_card_nonnegative

/-- Exact post-B2 accounting identity.  It contains no untracked credit: the
net charge is the selected center-plus-used-core ledger, plus the retained
nonnegative center-core correction, plus the literal unprocessed core. -/
theorem netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
    (choice : support.completionProfile.FullChoice) :
    support.assignedChargeProfile.netQuarterCharge =
      (support.assignedChargeProfile.centerQuarterCharge +
        ∑ vertex ∈ support.usedCore choice,
          support.assignedChargeProfile.coreQuarterChargeAt vertex) +
      ((∑ center ∈ support.centers,
          support.assignedChargeProfile.coreQuarterChargeAt center) +
        (support.centers.card : Int)) +
      support.remainingQuarterCharge choice := by
  exact Graph.AssignedSupportCharge.Profile.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
      support.assignedChargeProfile (support.usedCore choice)
      (support.usedCore_subset_core choice) support.centers_subset_core
      (support.usedCore_disjoint_centers choice)

/-- Exact full-family local balance, indexed by the duplicate-free finite
demand universe. -/
noncomputable def fullLocalQuarterBalance
    (choice : support.completionProfile.FullChoice) : Int := by
  letI : DecidableEq support.Demand := support.demands.decEq
  exact ∑ demand ∈ support.fullDemandSet,
    (support.entry demand).localQuarterBalance support.reserve
      (support.fullChosenLocalCandidate choice demand)

theorem fullLocalQuarterBalance_nonnegative
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.fullLocalQuarterBalance choice := by
  letI : DecidableEq support.Demand := support.demands.decEq
  unfold fullLocalQuarterBalance
  exact Finset.sum_nonneg fun demand _member =>
    TypeBLocalEntry.localQuarterBalance_nonnegative
      (support.entry demand) support.reserve
      (support.fullChosenLocalCandidate choice demand)

/-- Global no-double-counting transfer: the full local B1/B2 balance is
bounded by the sum of the actual center entries and the actual core charges
on their disjoint used support. -/
theorem fullLocalQuarterBalance_le_actualCharge
    (choice : support.completionProfile.FullChoice) :
    support.fullLocalQuarterBalance choice ≤
      (∑ demand ∈ support.fullDemandSet,
        Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
          ctx.G.object demand.1) +
      ∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex := by
  letI : DecidableEq support.Demand := support.demands.decEq
  unfold fullLocalQuarterBalance
  calc
    _ ≤ ∑ demand ∈ support.fullDemandSet,
        (Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
            ctx.G.object demand.1 +
          ∑ vertex ∈ support.fullActualCoreSupport choice demand,
            support.assignedChargeProfile.coreQuarterChargeAt vertex) := by
      apply Finset.sum_le_sum
      intro demand _member
      exact support.localQuarterBalance_le_actualCoreSupport demand
        (support.fullChosenLocalCandidate choice demand)
    _ = (∑ demand ∈ support.fullDemandSet,
          Graph.AssignedSupportCharge.Profile.centerQuarterChargeAt
            ctx.G.object demand.1) +
        ∑ demand ∈ support.fullDemandSet,
          ∑ vertex ∈ support.fullActualCoreSupport choice demand,
            support.assignedChargeProfile.coreQuarterChargeAt vertex := by
      rw [Finset.sum_add_distrib]
    _ = _ := by rw [← support.usedCore_charge_eq_sum choice]

/-- A full B2 choice makes the entire selected fan part of the actual graph
ledger nonnegative. -/
theorem processedFanCharge_nonnegative
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.assignedChargeProfile.centerQuarterCharge +
      ∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex := by
  have localNonnegative := support.fullLocalQuarterBalance_nonnegative choice
  have transfer := support.fullLocalQuarterBalance_le_actualCharge choice
  rw [support.fullCenterCharge_eq_centerQuarterCharge] at transfer
  omega

/-- Unconditional, exact state-space split after a rigorous full Type B
choice: either the desired net charge is already nonnegative, or the literal
remaining induced core has negative charge.  The latter is the only possible
post-ledger branch and is the input to the Type A component analysis. -/
theorem netQuarterCharge_nonnegative_or_remaining_negative
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
      support.remainingQuarterCharge choice < 0 := by
  exact Graph.AssignedSupportCharge.Profile.netQuarterCharge_nonnegative_or_remaining_negative
      support.assignedChargeProfile (support.usedCore choice)
      (support.usedCore_subset_core choice) support.centers_subset_core
      (support.usedCore_disjoint_centers choice)
      (support.processedFanCharge_nonnegative choice)

end TypeBAssignedSupport

/-- The three node-local graph-charge obligations.  The accumulated
predecessor is owned separately by `LedgerExtension`. -/
structure VerifiedTypeBAssignedCharge
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  processedNonnegative : ∀ (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice),
    0 ≤ support.assignedChargeProfile.centerQuarterCharge +
      ∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex
  exactPostLedger : ∀ (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice),
    support.assignedChargeProfile.netQuarterCharge =
      (support.assignedChargeProfile.centerQuarterCharge +
        ∑ vertex ∈ support.usedCore choice,
          support.assignedChargeProfile.coreQuarterChargeAt vertex) +
      ((∑ center ∈ support.centers,
          support.assignedChargeProfile.coreQuarterChargeAt center) +
        (support.centers.card : Int)) +
      support.remainingQuarterCharge choice
  total : ∀ (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice),
    0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
      support.remainingQuarterCharge choice < 0

abbrev VerifiedTypeBAssignedChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.LedgerExtension (VerifiedTypeBChoiceLedgerPrefix ctx)
    (fun _previous => VerifiedTypeBAssignedCharge ctx)

noncomputable def verifiedTypeBAssignedChargePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBChoiceLedgerPrefix ctx) :
    VerifiedTypeBAssignedChargePrefix ctx :=
  ⟨previous, {
    processedNonnegative := fun support choice =>
      support.processedFanCharge_nonnegative choice
    exactPostLedger := fun support choice =>
      support.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
        choice
    total := fun support choice =>
      support.netQuarterCharge_nonnegative_or_remaining_negative choice
  }⟩

theorem exists_verifiedTypeBAssignedChargePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedTypeBAssignedChargePrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedTypeBChoiceLedgerPrefix object baseline avoids
  exact ⟨ctx, verifiedTypeBAssignedChargePrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
