import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic
import StructuralExhaustion.Core.FiniteReceiverDischarge
import StructuralExhaustion.Graph.InducedSubgraph

namespace StructuralExhaustion.Graph.LowDegreeReceiverRouting

open StructuralExhaustion

universe u

/-!
# Low-degree receiver routing

An internal minimum-degree obstruction is exactly what could trap a connected
component away from low-degree receivers.  This file proves the reusable
graph-theoretic bridge: if a finite graph has no internal core of degree
`bound`, every vertex can reach a vertex of degree below `bound`.

Receiver existence is proved from one connected component.  Downstream proof
routing uses the resulting witness noncomputably, so compilation never asks
Lean to evaluate the generic finite reachability decision procedure.  No
paths, subsets, subgraphs, or routing functions are enumerated.
-/

variable {V : Type u}

namespace FiniteObject

variable (object : Graph.FiniteObject V)

/-- Every connected component of a graph with no internal `bound`-core
contains a vertex of degree below `bound`. -/
theorem exists_reachable_degree_lt
    (bound : Nat) (free : object.InternalMinDegreeFree bound)
    (vertex : V) :
    ∃ receiver : V,
      object.graph.Reachable vertex receiver ∧
        object.degree receiver < bound := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  by_contra unavailable
  push Not at unavailable
  let component := object.graph.connectedComponentMk vertex
  let componentVertices : Finset V := component.supp.toFinset
  have vertexMember : vertex ∈ componentVertices := by
    simp [componentVertices, component]
  have componentNonempty : Nonempty {other : V // other ∈ componentVertices} :=
    ⟨⟨vertex, vertexMember⟩⟩
  apply free
  refine ⟨componentVertices, ?_⟩
  let core := object.induceFinset componentVertices
  have minimum : bound ≤ core.minDegree := by
    letI : Nonempty {other : V // other ∈ componentVertices} :=
      componentNonempty
    apply core.le_minDegree_of_forall_le_degree bound
    intro other
    have otherInComponent : other.1 ∈ component.supp := by
      have member : other.1 ∈ component.supp.toFinset := by
        change other.1 ∈ componentVertices
        exact other.2
      exact Set.mem_toFinset.mp member
    have reachable : object.graph.Reachable vertex other.1 := by
      apply SimpleGraph.ConnectedComponent.exact
      exact otherInComponent.symm
    have ambientLower : bound ≤ object.degree other.1 := by
      exact unavailable other.1 reachable
    have neighborClosed : object.graph.neighborSet other.1 ⊆ component.supp := by
      intro neighbor adjacent
      exact (component.mem_supp_congr_adj adjacent).mp otherInComponent
    have degreeEq : core.degree other = object.degree other.1 := by
      rw [core.degree_eq_ncard_neighborSet,
        object.degree_eq_ncard_neighborSet]
      have neighborImage :
          Subtype.val '' core.graph.neighborSet other =
            object.graph.neighborSet other.1 := by
        ext neighbor
        constructor
        · rintro ⟨subneighbor, adjacent, rfl⟩
          simpa [core, Graph.FiniteObject.induceFinset] using adjacent
        · intro adjacent
          have neighborMember : neighbor ∈ componentVertices := by
            change neighbor ∈ component.supp.toFinset
            exact Set.mem_toFinset.mpr (neighborClosed adjacent)
          refine ⟨⟨neighbor, neighborMember⟩, ?_, rfl⟩
          simpa [core, Graph.FiniteObject.induceFinset] using adjacent
      calc
        (core.graph.neighborSet other).ncard =
            (Subtype.val '' core.graph.neighborSet other).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
        _ = (object.graph.neighborSet other.1).ncard := by rw [neighborImage]
    rw [degreeEq]
    exact ambientLower
  exact minimum

/-- Degree-three specialization used by the `3/7/11` discharge. -/
theorem exists_reachable_receiver
    (free : object.InternalMinDegreeFree 3) (vertex : V) :
    ∃ receiver : V,
      object.graph.Reachable vertex receiver ∧
        object.degree receiver ≤ 2 := by
  obtain ⟨receiver, reachable, degree⟩ :=
    exists_reachable_degree_lt object 3 free vertex
  exact ⟨receiver, reachable, by omega⟩

end FiniteObject

/-! ## Direct `3/7/11` discharge profile -/

/-- A finite subcubic graph with no internal degree-three core. -/
structure SubcubicProfile (object : Graph.FiniteObject V) : Prop where
  degree_le_three : ∀ vertex, object.degree vertex ≤ 3
  coreFree : object.InternalMinDegreeFree 3

namespace SubcubicProfile

variable {object : Graph.FiniteObject V} (profile : SubcubicProfile object)

def dischargeParameters : Core.FiniteReceiverDischarge.Parameters where
  sourceDegree := 3
  scale := 4
  scale_pos := by norm_num

noncomputable def dischargeInput : Core.FiniteReceiverDischarge.Input V where
  parameters := dischargeParameters
  vertices := object.input.vertices
  support := by
    letI : FinEnum V := object.input.vertices
    exact Finset.univ
  degree := object.degree
  degree_le_source := fun vertex _member => profile.degree_le_three vertex

noncomputable def receiverFor (vertex : V) : V :=
  Classical.choose
    (Graph.LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver
      object profile.coreFree vertex)

theorem receiverFor_reachable (vertex : V) :
    object.graph.Reachable vertex (profile.receiverFor vertex) :=
  (Classical.choose_spec
    (Graph.LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver
      object profile.coreFree vertex)).1

theorem receiverFor_degree_le_two (vertex : V) :
    object.degree (profile.receiverFor vertex) ≤ 2 :=
  (Classical.choose_spec
    (Graph.LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver
      object profile.coreFree vertex)).2

/-- Proof-selected receiver assignment.  The route is mathematical data, not
an evaluated search table; its existence is forced by `coreFree`. -/
noncomputable def dischargeRouting :
    Core.FiniteReceiverDischarge.Routing profile.dischargeInput where
  route := fun cubic => by
    refine ⟨profile.receiverFor cubic.1, ?_⟩
    rw [Core.FiniteReceiverDischarge.Input.mem_receiverSet_iff]
    constructor
    · letI : FinEnum V := object.input.vertices
      simp [dischargeInput]
    · have degree := profile.receiverFor_degree_le_two cubic.1
      simp [dischargeInput, dischargeParameters]
      omega

theorem dischargeRouting_reachable
    (cubic : {vertex // vertex ∈ profile.dischargeInput.sourceSet}) :
    object.graph.Reachable cubic.1
      (profile.dischargeRouting.route cubic).1 := by
  simpa [dischargeRouting] using profile.receiverFor_reachable cubic.1

abbrev Unsaturated : Prop := profile.dischargeRouting.Unsaturated

/-- A literal low-degree receiver whose assigned cubic load exceeds its
`3/7/11` capacity. -/
abbrev Saturated := profile.dischargeRouting.Saturated

/-- Literal total excess above the degree-dependent receiver capacities. -/
noncomputable def totalOverload : Nat :=
  profile.dischargeRouting.totalOverload

theorem saturated_or_unsaturated :
    Nonempty profile.Saturated ∨ profile.Unsaturated :=
  profile.dischargeRouting.saturated_or_unsaturated

theorem not_unsaturated_iff_nonempty_saturated :
    ¬profile.Unsaturated ↔ Nonempty profile.Saturated :=
  profile.dischargeRouting.not_unsaturated_iff_nonempty_saturated

/-- Exact graph-level unsaturated receiver discharge. -/
theorem signedCharge_nonnegative (unsaturated : profile.Unsaturated) :
    0 ≤ ∑ vertex ∈ profile.dischargeInput.support,
      profile.dischargeInput.signedCharge vertex :=
  profile.dischargeRouting.signedCharge_nonnegative unsaturated

theorem totalOverload_eq_zero_of_unsaturated
    (unsaturated : profile.Unsaturated) :
    profile.totalOverload = 0 :=
  profile.dischargeRouting.totalOverload_eq_zero_of_unsaturated unsaturated

/-- Unconditional receiver inequality, retaining the exact overload as the
Type A continuation quantity. -/
theorem neg_signedCharge_le_totalOverload :
    -(∑ vertex ∈ profile.dischargeInput.support,
      profile.dischargeInput.signedCharge vertex) ≤
        (profile.totalOverload : Int) :=
  profile.dischargeRouting.neg_signedCharge_le_totalOverload

end SubcubicProfile

end StructuralExhaustion.Graph.LowDegreeReceiverRouting
