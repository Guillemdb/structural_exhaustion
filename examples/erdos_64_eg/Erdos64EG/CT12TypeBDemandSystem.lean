import Erdos64EG.CT14CertificateClosedCandidate
import StructuralExhaustion.Core.DependentWeightedSelection
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Graph.RefinedFanLedger
import StructuralExhaustion.Graph.InducedCoreFanReserve

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Concrete finite Type B demand system

An assigned support supplies a finite set of actual centers and, at each
center, one of the two already verified local fan records.  The candidate
type, validity predicate, finiteness proof, and carrier support are derived
from the corresponding weighted selection profile.  None is an application
contract field.
-/

inductive TypeBLocalEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  | certificate (marked : CertificateClosedMarkedFan ctx)
  | positive (entry : PositiveDeficitMarkedFan ctx)

namespace TypeBLocalEntry

abbrev LocalCarrier
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :=
  Graph.FanClosedPort.LocalCarrier ctx.G.Vertex

def center
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :
    TypeBLocalEntry ctx → ctx.G.Vertex
  | .certificate marked => marked.fan.center
  | .positive entry => entry.fan.center

/-- The literal assigned-incidence predicate used to construct this local
entry.  Exposing it is essential for the global support layer: a local charge
calculation may only be used for the finite incidence assignment of the
support being discharged. -/
def Assigned
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :
    TypeBLocalEntry ctx →
      Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop
  | .certificate marked => marked.Assigned
  | .positive entry => entry.Assigned

def assignedDecidable
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx) :
    ∀ carrier, Decidable (entry.Assigned carrier) := by
  cases entry with
  | certificate marked => exact marked.assignedDecidable
  | positive entry => exact entry.assignedDecidable

/-- Core membership required for the local arithmetic to transfer to an
actual counted support.  Certificate candidates choose their core neighbours
through the effective reserve, whereas a positive-deficit formula uses the
whole ambient fan and therefore requires every fan neighbour to be counted. -/
def CoreCompatible
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (core : Finset ctx.G.Vertex) : TypeBLocalEntry ctx → Prop
  | .certificate _marked => True
  | .positive entry =>
      ∀ port : Graph.HighCenterPort.Port ctx.G.object entry.fan.center,
        Graph.HighCenterPort.endpoint ctx.G.object entry.fan.center port ∈ core

/-- Literal selectable-item type determined by one already verified local
branch.  The common lifted universe lets heterogeneous branches coexist in
one dependent CT12 family without erasing their item semantics. -/
def CandidateItem
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}} :
    TypeBLocalEntry ctx → Type u
  | .certificate marked =>
      ULift.{u, 0}
        (Graph.HighCenterPort.Port ctx.G.object marked.fan.center)
  | .positive entry =>
      Graph.HybridFanIncidence.Incidence
        (object := ctx.G.object) (center := entry.fan.center)
        (p13FanWindowProfile ctx entry.Assigned entry.assignedDecidable)

/-- The exact weighted selection profile belonging to a local branch. -/
noncomputable def selectionProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex) :
    (entry : TypeBLocalEntry ctx) →
      Core.FiniteWeightedSelection.Profile entry.CandidateItem ctx.G.Vertex
  | .certificate marked =>
      (marked.candidateProfile reserve.vertexReserve).uliftItems
  | .positive entry =>
      entry.candidateProfile reserve.incidenceReserve

@[simp]
theorem selectionProfile_certificate
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (marked : CertificateClosedMarkedFan ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex) :
    (TypeBLocalEntry.certificate marked).selectionProfile reserve =
      (marked.candidateProfile reserve.vertexReserve).uliftItems :=
  rfl

@[simp]
theorem selectionProfile_positive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : PositiveDeficitMarkedFan ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex) :
    (TypeBLocalEntry.positive entry).selectionProfile reserve =
      entry.candidateProfile reserve.incidenceReserve :=
  rfl

/-- The center is part of the fixed carrier support in either concrete local
branch. -/
theorem center_mem_baseSupport
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (entry : TypeBLocalEntry ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex) :
    entry.center ∈ (entry.selectionProfile reserve).baseSupport := by
  cases entry with
  | certificate marked =>
      simp [center, selectionProfile,
        Core.FiniteWeightedSelection.Profile.uliftItems,
        CertificateClosedMarkedFan.candidateProfile,
        Graph.CertificateClosedFanCandidate.Profile.selectionProfile]
  | positive entry =>
      simp [center, selectionProfile,
        PositiveDeficitMarkedFan.candidateProfile,
        Graph.HybridFanCandidate.profile, Graph.HybridFanCandidate.baseSupport]

/-- A selected certificate item is free in the literal vertex reserve even
after the heterogeneous candidate fibre is universe-lifted. -/
theorem certificate_selected_vertex_reserve_free
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (marked : CertificateClosedMarkedFan ctx)
    (reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex)
    (candidate : ((TypeBLocalEntry.certificate marked).selectionProfile
      reserve).Candidate)
    {port : Graph.HighCenterPort.Port ctx.G.object marked.fan.center}
    (selected : ULift.up port ∈ candidate.1) :
    ¬reserve.VertexUsed
      (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) := by
  have free := Core.FiniteWeightedSelection.Profile.selected_not_forbidden
    ((TypeBLocalEntry.certificate marked).selectionProfile reserve)
    candidate selected
  change ¬reserve.vertexReserve.Used
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port) at free
  change ¬reserve.vertexReserve.Used
    (Graph.HighCenterPort.endpoint ctx.G.object marked.fan.center port)
  simpa [selectionProfile,
    Core.FiniteWeightedSelection.Profile.uliftItems,
    CertificateClosedMarkedFan.candidateProfile,
    Graph.CertificateClosedFanCandidate.Profile.selectionProfile] using free

end TypeBLocalEntry

/-- Raw assigned Type B support data.  The finite center set makes duplicate
demands impossible, and the local entry sum expresses exactly the absence of
a fan-certificate residual center. -/
structure TypeBAssignedSupport
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  /-- Counted remainder vertices of the assigned support. -/
  vertices : Finset ctx.G.Vertex
  vertices_remainder : vertices ⊆ p13RemainderVertices ctx
  /-- Finite external/decorative incidences added to the induced core
  assignment.  `Assigned` below unions these with every internal core edge and
  filters the result by literal graph adjacency. -/
  assignedCarriers : Finset (Graph.FanClosedPort.LocalCarrier ctx.G.Vertex)
  centers : Finset ctx.G.Vertex
  centers_exact : centers = by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    exact vertices.filter fun center => 4 ≤ ctx.G.object.degree center
  entry : (center : {vertex // vertex ∈ centers}) → TypeBLocalEntry ctx
  entry_center : ∀ center, (entry center).center = center.1
  entry_assigned : ∀ center carrier,
    (entry center).Assigned carrier ↔
      ctx.G.object.graph.Adj carrier.1 carrier.2 ∧
        (carrier ∈ assignedCarriers ∨
          (carrier.1 ∈ vertices ∧ carrier.2 ∈ vertices))
  entry_coreCompatible : ∀ center, (entry center).CoreCompatible vertices
  /-- Only the pre-existing ordinary conflicts are input data. The refined
  vertex/incidence reserve is constructed canonically below. -/
  baseReserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex

namespace TypeBAssignedSupport

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (support : TypeBAssignedSupport ctx)

def assignedChargeProfile :
    Graph.AssignedSupportCharge.Profile ctx.G.object where
  core := support.vertices
  assignedCenters := support.centers

/-- Canonical refined reserve. It is not a contract field. -/
noncomputable def reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex :=
  Graph.InducedCoreFanReserve.reserve ctx.G.object
    support.assignedChargeProfile (p13CoveredVertices ctx) support.baseReserve

theorem reserve_excludes_external {vertex : ctx.G.Vertex}
    (outside : vertex ∉ support.vertices) :
    support.reserve.VertexUsed vertex :=
  Graph.InducedCoreFanReserve.vertexUsed_of_outside_core ctx.G.object
    support.assignedChargeProfile (p13CoveredVertices ctx)
      support.baseReserve outside

theorem reserve_excludes_center {vertex : ctx.G.Vertex}
    (center : vertex ∈ support.centers) :
    support.reserve.VertexUsed vertex :=
  Graph.InducedCoreFanReserve.vertexUsed_of_center ctx.G.object
    support.assignedChargeProfile (p13CoveredVertices ctx)
      support.baseReserve center

theorem reserve_free_nonWindow_ordinary
    {carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex}
    (free : ¬support.reserve.IncidenceUsed carrier)
    (nonWindow : carrier.2 ∉ p13CoveredVertices ctx) :
    Graph.InducedCoreFanReserve.OrdinaryAvailable ctx.G.object
      support.assignedChargeProfile carrier.2 :=
  Graph.InducedCoreFanReserve.incidence_free_ordinary_of_nonWindow ctx.G.object
    support.assignedChargeProfile (p13CoveredVertices ctx)
      support.baseReserve free nonWindow

abbrev Demand := {vertex : ctx.G.Vertex // vertex ∈ support.centers}

/-- The support's actual assigned-incidence predicate.  Every internal core
edge is assigned automatically; a finite extra set records window/decorative
incidences.  Non-edges are rejected definitionally. -/
def Assigned (carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex) : Prop :=
  ctx.G.object.graph.Adj carrier.1 carrier.2 ∧
    (carrier ∈ support.assignedCarriers ∨
      (carrier.1 ∈ support.vertices ∧ carrier.2 ∈ support.vertices))

def assignedDecidable : ∀ carrier, Decidable (support.Assigned carrier) := by
  intro carrier
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  unfold Assigned
  exact inferInstance

theorem centers_eq_high_filter : support.centers = by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    exact support.vertices.filter fun center => 4 ≤ ctx.G.object.degree center :=
  support.centers_exact

theorem demand_mem_vertices (demand : support.Demand) :
    demand.1 ∈ support.vertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member : demand.1 ∈ support.vertices.filter
      (fun center => 4 ≤ ctx.G.object.degree center) := by
    rw [← support.centers_exact]
    exact demand.2
  exact (Finset.mem_filter.mp member).1

theorem demand_mem_remainder (demand : support.Demand) :
    demand.1 ∈ p13RemainderVertices ctx :=
  support.vertices_remainder (support.demand_mem_vertices demand)

theorem demand_high (demand : support.Demand) :
    4 ≤ ctx.G.object.degree demand.1 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member : demand.1 ∈ support.vertices.filter
      (fun center => 4 ≤ ctx.G.object.degree center) := by
    rw [← support.centers_exact]
    exact demand.2
  exact (Finset.mem_filter.mp member).2

theorem localEntry_assigned_exact (demand : support.Demand) (carrier :
    Graph.FanClosedPort.LocalCarrier ctx.G.Vertex) :
    (support.entry demand).Assigned carrier ↔ support.Assigned carrier :=
  support.entry_assigned demand carrier

theorem localEntry_coreCompatible (demand : support.Demand) :
    (support.entry demand).CoreCompatible support.vertices :=
  support.entry_coreCompatible demand

@[implicit_reducible]
def demands : FinEnum support.Demand :=
  by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    exact Core.Enumeration.subtype ctx.G.object.input.vertices
      (fun vertex => vertex ∈ support.centers) (fun _vertex => inferInstance)

/-- Literal selectable-item type at one demand. -/
abbrev CandidateItem (demand : support.Demand) : Type u :=
  (support.entry demand).CandidateItem

/-- Exact local selection profile chosen by the concrete branch data. -/
noncomputable def selectionProfile (demand : support.Demand) :
    Core.FiniteWeightedSelection.Profile
      (support.CandidateItem demand) ctx.G.Vertex :=
  (support.entry demand).selectionProfile support.reserve

/-- Framework adapter deriving the dependent candidate family. -/
noncomputable def candidateFamily :
    Core.DependentWeightedSelection.Profile support.Demand ctx.G.Vertex where
  Item := support.CandidateItem
  demands := support.demands
  selection := support.selectionProfile

abbrev Candidate (demand : support.Demand) :=
  (support.candidateFamily).Candidate demand

/-- CT12-facing profile; every one of its fields is derived by the common
dependent-weighted-selection adapter. -/
noncomputable def ledgerProfile :
    Core.FiniteRefinedLedger.Profile support.Demand ctx.G.Vertex :=
  support.candidateFamily.refinedLedger

theorem candidate_finite (demand : support.Demand) :
    Finite (support.Candidate demand) :=
  support.candidateFamily.candidate_finite demand

/-- The concrete center schedule is no larger than the graph's explicit
vertex universe. -/
theorem demand_card_le_vertices :
    support.demands.card ≤ ctx.G.object.input.vertices.card := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  change (Core.Enumeration.subtype ctx.G.object.input.vertices
      (fun vertex => vertex ∈ support.centers)
      (fun _vertex => inferInstance)).card ≤
        ctx.G.object.input.vertices.card
  exact Core.Enumeration.subtype_card_le ctx.G.object.input.vertices
    (fun vertex => vertex ∈ support.centers) (fun _vertex => inferInstance)

private theorem entry_center_mem_support (demand : support.Demand)
    (candidate : support.Candidate demand) :
    (support.entry demand).center ∈
      (support.selectionProfile demand).carrierSupport candidate := by
  apply Core.FiniteWeightedSelection.Profile.baseSupport_subset
    (support.selectionProfile demand) candidate
  exact (support.entry demand).center_mem_baseSupport support.reserve

/-- Every derived candidate literally carries its scheduled center. -/
theorem candidate_center_mem_support (demand : support.Demand)
    (candidate : support.Candidate demand) :
    demand.1 ∈ (support.ledgerProfile.carrierSupport demand candidate) := by
  change demand.1 ∈ (support.selectionProfile demand).carrierSupport candidate
  rw [← support.entry_center demand]
  exact support.entry_center_mem_support demand candidate

/-- The demand center remains visible in the declared overlap universe even
when reserve conflicts make its valid candidate fibre empty. -/
theorem demand_center_mem_declaredSupport (demand : support.Demand) :
    demand.1 ∈ support.ledgerProfile.demandSupport demand := by
  change demand.1 ∈
    (support.selectionProfile demand).declaredCarrierSupport
  rw [← support.entry_center demand]
  apply Core.FiniteWeightedSelection.Profile.baseSupport_subset_declared
  exact (support.entry demand).center_mem_baseSupport support.reserve

end TypeBAssignedSupport

/-- Verified endpoint exposing the concrete branch-derived finite demand
system for every assigned Type B support. -/
structure VerifiedTypeBDemandSystemPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedTypeBCandidateFibresPrefix ctx
  candidateFinite : ∀ (support : TypeBAssignedSupport ctx)
    (demand : support.Demand), Finite (support.Candidate demand)
  centerCarried : ∀ (support : TypeBAssignedSupport ctx)
    (demand : support.Demand) (candidate : support.Candidate demand),
      demand.1 ∈ support.ledgerProfile.carrierSupport demand candidate

noncomputable def verifiedTypeBDemandSystemPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedTypeBCandidateFibresPrefix ctx) :
    VerifiedTypeBDemandSystemPrefix ctx where
  previous := previous
  candidateFinite := fun support demand => support.candidate_finite demand
  centerCarried := fun support demand candidate =>
    support.candidate_center_mem_support demand candidate

theorem exists_verifiedTypeBDemandSystemPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedTypeBDemandSystemPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedTypeBCandidateFibresPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedTypeBDemandSystemPrefix ctx previous⟩

end Erdos64EG.Internal
