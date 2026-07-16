import StructuralExhaustion.Graph.LowDegreeReceiverRouting
import StructuralExhaustion.Graph.NegativeSupportHandoff
import StructuralExhaustion.Graph.OrderedBFSTree

namespace StructuralExhaustion.Graph.TypeACanonicalReceiverTrace

open StructuralExhaustion

universe u

variable {V : Type u} (object : FiniteObject V)

/-!
# Canonical Type A receiver traces

This is the first graph-owned producer required by declared coordinate clause
D5.  Starting from a proof-carrying Type A support, it runs one ordered BFS
from each internal cubic vertex and selects the first vertex in the first BFS
layer whose internal degree is at most two.  The retained tree walk therefore
stays in the internal degree-three part until its final vertex.

Only the supplied support and its induced graph are scanned.  No path family,
subgraph family, context universe, or graph universe is enumerated.
-/

/-- Exact structural input for the receiver-trace part of a Type A support.
The ambient-cubic clause records `sigma(X)=0`; `degree_le_three` and
`coreFree` are the internal support facts used by the routing theorem. -/
structure SupportProfile : Type u where
  support : Finset V
  connected : NegativeSupportHandoff.ConnectedOn object support
  ambient_cubic : ∀ vertex ∈ support, object.degree vertex = 3
  degree_le_three : ∀ vertex : {value : V // value ∈ support},
    (object.induceFinset support).degree vertex ≤ 3
  coreFree : (object.induceFinset support).InternalMinDegreeFree 3

namespace SupportProfile

variable (profile : SupportProfile object)

abbrev Vertex := {value : V // value ∈ profile.support}

noncomputable abbrev supportObject : FiniteObject profile.Vertex :=
  object.induceFinset profile.support

theorem support_nonempty : profile.support.Nonempty := profile.connected.1

theorem supportObject_preconnected : profile.supportObject object |>.graph.Preconnected := by
  intro left right
  obtain ⟨path, _isPath, contained⟩ :=
    profile.connected.2 left.2 right.2
  let lifted := path.induce {vertex | vertex ∈ profile.support} (by
    intro vertex member
    exact contained vertex member)
  exact ⟨lifted⟩

/-- One stored connectivity certificate shared definitionally by every BFS
trace and downstream dependent coordinate. -/
noncomputable def preconnected :
    (profile.supportObject object).graph.Preconnected :=
  profile.supportObject_preconnected object

/-- Internal degree-three vertices that require receiver traces. -/
abbrev Cubic :=
  {vertex : profile.Vertex //
    (profile.supportObject object).degree vertex = 3}

noncomputable def cubicDecidable (vertex : profile.Vertex) :
    Decidable ((profile.supportObject object).degree vertex = 3) :=
  inferInstance

/-- Exact declared-order enumeration of the internal cubic sources. -/
@[implicit_reducible]
noncomputable def cubics : FinEnum (profile.Cubic object) :=
  Core.Enumeration.subtype
    (profile.supportObject object).input.vertices
    (fun vertex => (profile.supportObject object).degree vertex = 3)
    (profile.cubicDecidable object)

noncomputable def receiverVertices : Finset profile.Vertex := by
  letI : DecidableEq profile.Vertex :=
    (profile.supportObject object).input.vertices.decEq
  exact (profile.supportObject object).vertexFinset.filter fun vertex =>
    (profile.supportObject object).degree vertex ≤ 2

theorem receiverVertices_nonempty :
    (profile.receiverVertices object).Nonempty := by
  obtain ⟨root, rootMem⟩ := profile.support_nonempty
  let rootVertex : profile.Vertex := ⟨root, rootMem⟩
  obtain ⟨receiver, _reachable, degree⟩ :=
    LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver
      (profile.supportObject object) profile.coreFree rootVertex
  refine ⟨receiver, ?_⟩
  simp [receiverVertices, degree,
    (profile.supportObject object).mem_vertexFinset]

/-- One ordered BFS rooted at an actual internal cubic vertex. -/
noncomputable def bfs (cubic : profile.Cubic object) :
    OrderedBFSTree.Profile (profile.supportObject object) where
  root := cubic.1

/-- First declared receiver in the first occupied BFS layer. -/
noncomputable def receiverSelection (cubic : profile.Cubic object) :
    (profile.bfs object cubic).TargetSelection
      (profile.preconnected object)
      (profile.receiverVertices object) :=
  (profile.bfs object cubic).selectTarget
    (profile.preconnected object)
    (profile.receiverVertices object)
    (profile.receiverVertices_nonempty object)

/-- Canonical internal trace from `u` to its selected receiver. -/
noncomputable def trace (cubic : profile.Cubic object) :
    (profile.supportObject object).graph.Walk cubic.1
      (profile.receiverSelection object cubic).vertex :=
  (profile.bfs object cubic).treeWalk
    (profile.preconnected object)
    (profile.receiverSelection object cubic).vertex

theorem trace_isPath (cubic : profile.Cubic object) :
    (profile.trace object cubic).IsPath :=
  (profile.bfs object cubic).treeWalk_isPath
    (profile.preconnected object)
    (profile.receiverSelection object cubic).vertex

/-- The cubic root is a literal member of the supplied Type A support. -/
theorem cubic_mem_support (cubic : profile.Cubic object) :
    cubic.1.1 ∈ profile.support :=
  cubic.1.2

/-- The selected low-degree receiver is a literal member of the same support. -/
theorem receiver_mem_support (cubic : profile.Cubic object) :
    (profile.receiverSelection object cubic).vertex.1 ∈ profile.support :=
  (profile.receiverSelection object cubic).vertex.2

theorem receiver_degree_le_two (cubic : profile.Cubic object) :
    (profile.supportObject object).degree
      (profile.receiverSelection object cubic).vertex ≤ 2 := by
  have member :=
    (profile.receiverSelection object cubic).vertex_mem
  simpa [receiverVertices] using (Finset.mem_filter.mp member).2

/-- The internal cubic root cannot already be the selected low-degree
receiver.  Consequently the retained trace contains at least one edge. -/
theorem cubic_ne_receiver (cubic : profile.Cubic object) :
    cubic.1 ≠ (profile.receiverSelection object cubic).vertex := by
  intro equal
  have cubicDegree := cubic.2
  have receiverDegree := profile.receiver_degree_le_two object cubic
  rw [equal] at cubicDegree
  omega

theorem trace_length_pos (cubic : profile.Cubic object) :
    0 < (profile.trace object cubic).length := by
  exact SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (SimpleGraph.Walk.not_nil_of_ne (profile.cubic_ne_receiver object cubic))

/-- Both endpoints occur in the literal ordered trace support. -/
theorem cubic_mem_trace_support (cubic : profile.Cubic object) :
    cubic.1 ∈ (profile.trace object cubic).support := by
  simpa using (profile.trace object cubic).getVert_mem_support 0

theorem receiver_mem_trace_support (cubic : profile.Cubic object) :
    (profile.receiverSelection object cubic).vertex ∈
      (profile.trace object cubic).support := by
  simpa only [SimpleGraph.Walk.getVert_length] using
    (profile.trace object cubic).getVert_mem_support
      (profile.trace object cubic).length

/-- The trace schedule has no repeated vertices. -/
theorem trace_support_nodup (cubic : profile.Cubic object) :
    (profile.trace object cubic).support.Nodup :=
  (profile.trace_isPath object cubic).support_nodup

/-- Consecutive stored positions are adjacent in the original ambient graph,
not merely in an abstract response universe. -/
theorem trace_successive_ambient_adjacent (cubic : profile.Cubic object)
    {index : Nat} (bound : index < (profile.trace object cubic).length) :
    object.graph.Adj
      ((profile.trace object cubic).getVert index).1
      ((profile.trace object cubic).getVert (index + 1)).1 := by
  exact (profile.trace object cubic).adj_getVert_succ bound

/-- The ordered BFS trace first meets the explicit receiver set at its final
vertex.  This is the proof-carrying form consumed by the later D5 coordinate
producer; it does not enumerate alternative paths. -/
theorem receiverSelection_first_lands (cubic : profile.Cubic object) :
    (profile.receiverSelection object cubic).vertex ∈
        profile.receiverVertices object ∧
      ∀ index < ((profile.bfs object cubic).treeWalk
          (profile.preconnected object)
          (profile.receiverSelection object cubic).vertex).length,
        ((profile.bfs object cubic).treeWalk
          (profile.preconnected object)
          (profile.receiverSelection object cubic).vertex).getVert index ∉
          profile.receiverVertices object := by
  exact OrderedBFSTree.Profile.TargetSelection.treeWalk_first_lands
    (profile.bfs object cubic) (profile.receiverSelection object cubic)

/-- Every strict prefix vertex of the selected trace has internal degree
exactly three. -/
theorem receiverSelection_internal_degree_eq_three
    (cubic : profile.Cubic object) (index : Nat)
    (before : index < ((profile.bfs object cubic).treeWalk
      (profile.preconnected object)
      (profile.receiverSelection object cubic).vertex).length) :
    (profile.supportObject object).degree
      (((profile.bfs object cubic).treeWalk
        (profile.preconnected object)
        (profile.receiverSelection object cubic).vertex).getVert index) = 3 := by
  let vertex := ((profile.bfs object cubic).treeWalk
    (profile.preconnected object)
    (profile.receiverSelection object cubic).vertex).getVert index
  have notReceiver : vertex ∉ profile.receiverVertices object :=
    (profile.receiverSelection_first_lands object cubic).2 index before
  have notLeTwo : ¬(profile.supportObject object).degree vertex ≤ 2 := by
    intro degree
    apply notReceiver
    rw [receiverVertices, Finset.mem_filter]
    exact ⟨(profile.supportObject object).mem_vertexFinset vertex, degree⟩
  have upper : (profile.supportObject object).degree vertex ≤ 3 :=
    profile.degree_le_three vertex
  have lower : 3 ≤ (profile.supportObject object).degree vertex := by
    omega
  change (profile.supportObject object).degree vertex = 3
  exact Nat.le_antisymm upper lower

/-- The selected trace is no longer than any supplied trace from the same
cubic root to an internal low-degree receiver. -/
theorem trace_shortest_to_receiver (cubic : profile.Cubic object)
    (receiver : profile.Vertex)
    (degree : (profile.supportObject object).degree receiver ≤ 2)
    (candidate : (profile.supportObject object).graph.Walk cubic.1 receiver) :
    (profile.trace object cubic).length ≤ candidate.length := by
  have member : receiver ∈ profile.receiverVertices object := by
    rw [receiverVertices, Finset.mem_filter]
    exact ⟨(profile.supportObject object).mem_vertexFinset receiver, degree⟩
  exact OrderedBFSTree.Profile.TargetSelection.shortest_to_target
    (profile.bfs object cubic) (profile.receiverSelection object cubic)
    member candidate

/-- Static work envelope: one ordered BFS of at most `|X|` levels for every
internal cubic source. -/
noncomputable def visibleChecks : Nat :=
  profile.support.card ^ 2 * (profile.support.card + 1)

theorem visibleChecks_polynomial :
    profile.visibleChecks ≤
      object.input.vertices.card ^ 2 *
        (object.input.vertices.card + 1) := by
  have supportLe : profile.support.card ≤ object.input.vertices.card := by
    rw [← object.card_vertexFinset]
    apply Finset.card_le_card
    intro vertex _member
    exact object.mem_vertexFinset vertex
  unfold visibleChecks
  exact Nat.mul_le_mul (Nat.pow_le_pow_left supportLe 2)
    (Nat.add_le_add_right supportLe 1)

end SupportProfile

end StructuralExhaustion.Graph.TypeACanonicalReceiverTrace
