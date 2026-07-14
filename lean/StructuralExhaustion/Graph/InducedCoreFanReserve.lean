import StructuralExhaustion.Graph.AssignedSupportCharge
import StructuralExhaustion.Graph.RefinedFanLedger

namespace StructuralExhaustion.Graph.InducedCoreFanReserve

open StructuralExhaustion

universe u

/-!
# Canonical reserve for an induced-core fan ledger

The reserve is derived from literal graph data. Certificate selections may
use only ordinary core vertices. A non-window incidence may be selected only
when its remote endpoint is an ordinary core vertex, is outside every assigned
high-center fan neighbourhood, and has at least two quarter-units of actual
induced-core charge. Thus local half-credit can later be injected into the
global charge sum without an application-supplied safety certificate.
-/

variable {V : Type u} (object : FiniteObject V)
variable (profile : AssignedSupportCharge.Profile object)

def OrdinaryAvailable (vertex : V) : Prop :=
  vertex ∈ profile.core ∧
    vertex ∉ profile.assignedCenters ∧
    (∀ center ∈ profile.assignedCenters,
      ¬object.graph.Adj center vertex) ∧
    2 ≤ profile.coreQuarterChargeAt vertex

noncomputable def ordinaryAvailableDecidable :
    ∀ vertex, Decidable (OrdinaryAvailable object profile vertex) := by
  intro vertex
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold OrdinaryAvailable
  infer_instance

/-- The unique refined reserve determined by a base reserve, a counted core,
its assigned high centers, and the finite window set. -/
noncomputable def reserve (covered : Finset V)
    (base : RefinedFanLedger.Reserve V) : RefinedFanLedger.Reserve V where
  VertexUsed := fun vertex =>
    base.VertexUsed vertex ∨ vertex ∉ profile.core ∨
      vertex ∈ profile.assignedCenters
  vertexUsedDecidable := fun vertex => by
    letI : DecidableEq V := object.input.vertices.decEq
    letI : Decidable (base.VertexUsed vertex) :=
      base.vertexUsedDecidable vertex
    infer_instance
  IncidenceUsed := fun carrier =>
    base.IncidenceUsed carrier ∨
      (carrier.2 ∉ covered ∧
        ¬OrdinaryAvailable object profile carrier.2)
  incidenceUsedDecidable := fun carrier => by
    letI : DecidableEq V := object.input.vertices.decEq
    letI : Decidable (base.IncidenceUsed carrier) :=
      base.incidenceUsedDecidable carrier
    letI : Decidable (OrdinaryAvailable object profile carrier.2) :=
      ordinaryAvailableDecidable object profile carrier.2
    infer_instance

theorem vertexUsed_of_outside_core (covered : Finset V)
    (base : RefinedFanLedger.Reserve V) {vertex : V}
    (outside : vertex ∉ profile.core) :
    (reserve object profile covered base).VertexUsed vertex :=
  Or.inr (Or.inl outside)

theorem vertexUsed_of_center (covered : Finset V)
    (base : RefinedFanLedger.Reserve V) {vertex : V}
    (center : vertex ∈ profile.assignedCenters) :
    (reserve object profile covered base).VertexUsed vertex :=
  Or.inr (Or.inr center)

theorem vertex_free_mem_core_not_center (covered : Finset V)
    (base : RefinedFanLedger.Reserve V) {vertex : V}
    (free : ¬(reserve object profile covered base).VertexUsed vertex) :
    vertex ∈ profile.core ∧ vertex ∉ profile.assignedCenters := by
  constructor
  · by_contra outside
    exact free (vertexUsed_of_outside_core object profile covered base outside)
  · intro center
    exact free (vertexUsed_of_center object profile covered base center)

theorem incidenceUsed_of_unsafe_nonWindow (covered : Finset V)
    (base : RefinedFanLedger.Reserve V)
    {carrier : FanClosedPort.LocalCarrier V}
    (nonWindow : carrier.2 ∉ covered)
    (notAvailable : ¬OrdinaryAvailable object profile carrier.2) :
    (reserve object profile covered base).IncidenceUsed carrier :=
  Or.inr ⟨nonWindow, notAvailable⟩

theorem incidence_free_ordinary_of_nonWindow (covered : Finset V)
    (base : RefinedFanLedger.Reserve V)
    {carrier : FanClosedPort.LocalCarrier V}
    (free : ¬(reserve object profile covered base).IncidenceUsed carrier)
    (nonWindow : carrier.2 ∉ covered) :
    OrdinaryAvailable object profile carrier.2 := by
  by_contra notAvailable
  exact free (incidenceUsed_of_unsafe_nonWindow object profile covered base
    nonWindow notAvailable)

end StructuralExhaustion.Graph.InducedCoreFanReserve
