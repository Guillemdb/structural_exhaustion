import StructuralExhaustion.Graph.Cycle

namespace StructuralExhaustion.Graph

universe u

open scoped Sym2

/-!
# Edge-rooted return paths

An edge-rooted return stores a Mathlib simple path in the graph obtained by
deleting the root edge.  The root edge can therefore be restored to obtain a
simple cycle, and deleting one edge of a simple cycle produces the converse
return.  These operations inspect only the supplied walk certificate.
-/

/-- A simple return from the head of an oriented root edge to its tail in the
graph with that edge deleted. -/
structure EdgeRootedReturn {V : Type u} (G : SimpleGraph V)
    (LengthOK : Nat → Prop) where
  dart : G.Dart
  path : (G.deleteEdges {s(dart.fst, dart.snd)}).Walk dart.snd dart.fst
  isPath : path.IsPath
  length_ok : LengthOK path.length

/-- Existence of an edge-rooted return whose length satisfies `LengthOK`. -/
def HasEdgeRootedReturn {V : Type u} (G : SimpleGraph V)
    (LengthOK : Nat → Prop) : Prop :=
  Nonempty (EdgeRootedReturn G LengthOK)

/-- A simple return for one fixed oriented edge.  Unlike
`EdgeRootedReturn`, the dart is an index rather than certificate data; this
is the convenient output of a proved non-bridge fact. -/
structure DartReturn {V : Type u} (G : SimpleGraph V) (dart : G.Dart) where
  path : (G.deleteEdges {dart.edge}).Walk dart.snd dart.fst
  isPath : path.IsPath

namespace DartReturn

variable {V : Type u} {G : SimpleGraph V} {dart : G.Dart}

/-- A non-bridge supplies a simple return in the graph with that one edge
deleted.  This uses Mathlib's reachability-to-path theorem and classical
choice on the proved existential; it does not enumerate walks. -/
noncomputable def ofNotBridge
    (notBridge : ¬G.IsBridge dart.edge) : DartReturn G dart := by
  have reachableForward :
      (G.deleteEdges {dart.edge}).Reachable dart.fst dart.snd := by
    exact Classical.not_not.mp (by
      simpa [SimpleGraph.isBridge_iff, SimpleGraph.Dart.edge] using notBridge)
  let witness := reachableForward.symm.exists_isPath
  exact ⟨Classical.choose witness, Classical.choose_spec witness⟩

/-- Forget the fixed-dart index and regard a return as an unrestricted
edge-rooted certificate. -/
def toEdgeRootedReturn (returnPath : DartReturn G dart) :
    EdgeRootedReturn G (fun _length => True) where
  dart := dart
  path := returnPath.path
  isPath := returnPath.isPath
  length_ok := trivial

end DartReturn

/-- The exact return-length set rooted at one oriented edge. -/
def edgeReturnSet {V : Type u} (G : SimpleGraph V)
    (dart : G.Dart) : Set Nat :=
  {length | ∃ path : (G.deleteEdges {s(dart.fst, dart.snd)}).Walk
      dart.snd dart.fst, path.IsPath ∧ path.length = length}

namespace EdgeRootedReturn

variable {V : Type u} {G : SimpleGraph V} {LengthOK : Nat → Prop}

/-- Regard the deleted-edge return as a walk in the ambient graph. -/
def ambientPath (certificate : EdgeRootedReturn G LengthOK) :
    G.Walk certificate.dart.snd certificate.dart.fst :=
  certificate.path.mapLe (G.deleteEdges_le {s(certificate.dart.fst,
    certificate.dart.snd)})

theorem ambientPath_isPath (certificate : EdgeRootedReturn G LengthOK) :
    certificate.ambientPath.IsPath :=
  certificate.isPath.mapLe _

/-- The ambient view of a return still avoids its root edge. -/
theorem root_not_mem_path (certificate : EdgeRootedReturn G LengthOK) :
    s(certificate.dart.fst, certificate.dart.snd) ∉
      certificate.ambientPath.edges := by
  rw [ambientPath, SimpleGraph.Walk.edges_mapLe_eq_edges]
  intro rootMember
  have edgeMember := certificate.path.edges_subset_edgeSet rootMember
  simp [SimpleGraph.edgeSet_deleteEdges] at edgeMember

/-- Restore the root edge to close an edge-rooted return. -/
def cycle (certificate : EdgeRootedReturn G LengthOK) :
    G.Walk certificate.dart.fst certificate.dart.fst :=
  .cons certificate.dart.adj certificate.ambientPath

theorem cycle_isCycle (certificate : EdgeRootedReturn G LengthOK) :
    certificate.cycle.IsCycle := by
  exact (SimpleGraph.Walk.cons_isCycle_iff certificate.ambientPath
    certificate.dart.adj).2
      ⟨certificate.ambientPath_isPath, certificate.root_not_mem_path⟩

theorem cycle_length (certificate : EdgeRootedReturn G LengthOK) :
    certificate.cycle.length = certificate.path.length + 1 := by
  rw [cycle, SimpleGraph.Walk.length_cons]
  change (certificate.path.map _).length + 1 = certificate.path.length + 1
  rw [SimpleGraph.Walk.length_map]

/-- Delete the first edge of a concrete simple cycle to obtain its rooted
return certificate. -/
def ofCycle (cycle : CycleWithLength G LengthOK) :
    EdgeRootedReturn G (fun length => LengthOK (length + 1)) := by
  have notNil := cycle.isCycle.not_nil
  let dart : G.Dart := ⟨(cycle.vertex, cycle.walk.snd),
    cycle.walk.adj_snd notNil⟩
  have rebuiltCycle :
      (SimpleGraph.Walk.cons (cycle.walk.adj_snd notNil)
        cycle.walk.tail).IsCycle := by
    rw [cycle.walk.cons_tail_eq notNil]
    exact cycle.isCycle
  have tailData : cycle.walk.tail.IsPath ∧
      s(cycle.vertex, cycle.walk.snd) ∉ cycle.walk.tail.edges :=
    (SimpleGraph.Walk.cons_isCycle_iff cycle.walk.tail
      (cycle.walk.adj_snd notNil)).1 rebuiltCycle
  let path := cycle.walk.tail.toDeleteEdge
    s(cycle.vertex, cycle.walk.snd) tailData.2
  refine {
    dart := dart
    path := path
    isPath := ?_
    length_ok := ?_
  }
  · dsimp [path]
    apply tailData.1.toDeleteEdges
  · dsimp [path]
    rw [SimpleGraph.Walk.length_transfer]
    rw [cycle.walk.length_tail_add_one notNil]
    exact cycle.length_ok

end EdgeRootedReturn

/-- Removing the first edge of a certified simple cycle and restoring the root
edge are inverse at the level of accepted lengths. -/
theorem hasCycleWithLength_iff_hasEdgeRootedReturn
    {V : Type u} (G : SimpleGraph V) (LengthOK : Nat → Prop) :
    HasCycleWithLength G LengthOK ↔
      HasEdgeRootedReturn G (fun length => LengthOK (length + 1)) := by
  constructor
  · rintro ⟨cycle⟩
    exact ⟨EdgeRootedReturn.ofCycle cycle⟩
  · rintro ⟨certificate⟩
    exact ⟨{
      vertex := certificate.dart.fst
      walk := certificate.cycle
      isCycle := certificate.cycle_isCycle
      length_ok := by
        rw [certificate.cycle_length]
        exact certificate.length_ok
    }⟩

/-- Set-membership form of the existential edge-rooted return predicate. -/
theorem hasEdgeRootedReturn_iff_exists_mem_returnSet
    {V : Type u} (G : SimpleGraph V) (LengthOK : Nat → Prop) :
    HasEdgeRootedReturn G LengthOK ↔
      ∃ dart : G.Dart, ∃ length ∈ edgeReturnSet G dart, LengthOK length := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.dart, certificate.path.length,
      ⟨certificate.path, certificate.isPath, rfl⟩,
      certificate.length_ok⟩
  · rintro ⟨dart, length, ⟨path, isPath, pathLength⟩, lengthOK⟩
    refine ⟨⟨dart, path, isPath, ?_⟩⟩
    rw [pathLength]
    exact lengthOK

/-- Exact avoidance form: every rooted return set is disjoint from the
predecessors of the accepted cycle lengths. -/
theorem noCycleWithLength_iff_returnSets_disjoint
    {V : Type u} (G : SimpleGraph V) (LengthOK : Nat → Prop) :
    ¬ HasCycleWithLength G LengthOK ↔
      ∀ dart : G.Dart,
        Disjoint (edgeReturnSet G dart) {length | LengthOK (length + 1)} := by
  rw [hasCycleWithLength_iff_hasEdgeRootedReturn]
  rw [hasEdgeRootedReturn_iff_exists_mem_returnSet]
  constructor
  · intro noReturn dart
    rw [Set.disjoint_left]
    intro length inReturn lengthOK
    exact noReturn ⟨dart, length, inReturn, lengthOK⟩
  · intro disjoint hasReturn
    obtain ⟨dart, length, inReturn, lengthOK⟩ := hasReturn
    exact (Set.disjoint_left.mp (disjoint dart)) inReturn lengthOK

end StructuralExhaustion.Graph
