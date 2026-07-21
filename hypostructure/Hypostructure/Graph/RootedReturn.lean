import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Hypostructure.Graph.Target

/-!
# Edge-rooted return target algebra

An edge-rooted return is a Mathlib simple path from the head of an oriented
edge back to its tail after deleting that undirected edge. Restoring the root
edge produces a simple cycle, while deleting the first edge of a simple cycle
produces the converse return. This file proves only that semantic dictionary;
finite discovery belongs to CT1.
-/

namespace Hypostructure.Graph

universe u

open scoped Sym2

/-- The return-length predicate obtained by shifting a cycle-length predicate
back by the restored root edge. -/
def ShiftedCycleLength (CycleLengthOK : Nat → Prop)
    (returnLength : Nat) : Prop :=
  CycleLengthOK (returnLength + 1)

/-- The set of return lengths whose successor is accepted as a cycle length. -/
def shiftedAcceptedSet (CycleLengthOK : Nat → Prop) : Set Nat :=
  {returnLength | ShiftedCycleLength CycleLengthOK returnLength}

/-- A simple return from the head of an oriented root edge to its tail in the
graph obtained by deleting that edge. -/
structure EdgeRootedReturn (object : FiniteObject.{u})
    (ReturnLengthOK : Nat → Prop) where
  dart : object.graph.Dart
  path : (object.graph.deleteEdges {dart.edge}).Walk dart.snd dart.fst
  isPath : path.IsPath
  length_ok : ReturnLengthOK path.length

/-- Existence of one accepted edge-rooted return. -/
def HasEdgeRootedReturn (object : FiniteObject.{u})
    (ReturnLengthOK : Nat → Prop) : Prop :=
  Nonempty (EdgeRootedReturn object ReturnLengthOK)

/-- The exact set of simple return lengths rooted at one oriented edge. -/
def returnLengthSet (object : FiniteObject.{u})
    (dart : object.graph.Dart) : Set Nat :=
  {length | ∃ path : (object.graph.deleteEdges {dart.edge}).Walk
      dart.snd dart.fst, path.IsPath ∧ path.length = length}

namespace EdgeRootedReturn

variable {object : FiniteObject.{u}}
variable {ReturnLengthOK OtherLengthOK : Nat → Prop}

/-- Change only the accepted-length predicate, retaining the exact dart and
deleted-edge path. -/
def mapLengthPredicate
    (certificate : EdgeRootedReturn object ReturnLengthOK)
    (mapAccepted : ∀ length, ReturnLengthOK length → OtherLengthOK length) :
    EdgeRootedReturn object OtherLengthOK where
  dart := certificate.dart
  path := certificate.path
  isPath := certificate.isPath
  length_ok := mapAccepted certificate.path.length certificate.length_ok

/-- Regard the deleted-edge return as a walk in the ambient graph. -/
def ambientPath (certificate : EdgeRootedReturn object ReturnLengthOK) :
    object.graph.Walk certificate.dart.snd certificate.dart.fst :=
  certificate.path.mapLe (object.graph.deleteEdges_le {certificate.dart.edge})

/-- The ambient view of the return remains a simple path. -/
theorem ambientPath_isPath
    (certificate : EdgeRootedReturn object ReturnLengthOK) :
    certificate.ambientPath.IsPath :=
  certificate.isPath.mapLe _

/-- The ambient return still avoids its deleted root edge. -/
theorem root_not_mem_ambientPath
    (certificate : EdgeRootedReturn object ReturnLengthOK) :
    certificate.dart.edge ∉ certificate.ambientPath.edges := by
  rw [ambientPath, SimpleGraph.Walk.edges_mapLe_eq_edges]
  intro rootMember
  have edgeMember := certificate.path.edges_subset_edgeSet rootMember
  simp [SimpleGraph.edgeSet_deleteEdges] at edgeMember

/-- Restore the oriented root edge in front of its reverse return path. -/
def cycle (certificate : EdgeRootedReturn object ReturnLengthOK) :
    object.graph.Walk certificate.dart.fst certificate.dart.fst :=
  .cons certificate.dart.adj certificate.ambientPath

/-- Restoring the root edge closes an exact simple cycle. -/
theorem cycle_isCycle
    (certificate : EdgeRootedReturn object ReturnLengthOK) :
    certificate.cycle.IsCycle := by
  exact (SimpleGraph.Walk.cons_isCycle_iff certificate.ambientPath
    certificate.dart.adj).2
      ⟨certificate.ambientPath_isPath,
        certificate.root_not_mem_ambientPath⟩

/-- The restored cycle has exactly one edge more than the return path. -/
theorem cycle_length
    (certificate : EdgeRootedReturn object ReturnLengthOK) :
    certificate.cycle.length = certificate.path.length + 1 := by
  rw [cycle, SimpleGraph.Walk.length_cons]
  change (certificate.path.map _).length + 1 =
    certificate.path.length + 1
  rw [SimpleGraph.Walk.length_map]

/-- Delete the first edge of a supplied simple cycle. Its tail is a simple
reverse return in the graph with that edge deleted. -/
def ofCycle {CycleLengthOK : Nat → Prop}
    (certificate : CycleCertificate object CycleLengthOK) :
    EdgeRootedReturn object (ShiftedCycleLength CycleLengthOK) := by
  have notNil := certificate.isCycle.not_nil
  let dart : object.graph.Dart :=
    ⟨(certificate.vertex, certificate.walk.snd),
      certificate.walk.adj_snd notNil⟩
  have rebuiltCycle :
      (SimpleGraph.Walk.cons (certificate.walk.adj_snd notNil)
        certificate.walk.tail).IsCycle := by
    rw [certificate.walk.cons_tail_eq notNil]
    exact certificate.isCycle
  have tailData : certificate.walk.tail.IsPath ∧
      dart.edge ∉ certificate.walk.tail.edges := by
    exact (SimpleGraph.Walk.cons_isCycle_iff certificate.walk.tail
      (certificate.walk.adj_snd notNil)).1 rebuiltCycle
  let path := certificate.walk.tail.toDeleteEdge dart.edge tailData.2
  refine {
    dart := dart
    path := path
    isPath := ?_
    length_ok := ?_
  }
  · dsimp [path]
    apply tailData.1.toDeleteEdges
  · dsimp [ShiftedCycleLength, path]
    rw [SimpleGraph.Walk.length_transfer]
    rw [certificate.walk.length_tail_add_one notNil]
    exact certificate.length_ok

end EdgeRootedReturn

/-- A cycle with accepted length is exactly a rooted return whose length plus
the restored edge is accepted. -/
theorem hasCycleWithLength_iff_hasEdgeRootedReturn
    (CycleLengthOK : Nat → Prop) (object : FiniteObject.{u}) :
    HasCycleWithLength CycleLengthOK object ↔
      HasEdgeRootedReturn object (ShiftedCycleLength CycleLengthOK) := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨EdgeRootedReturn.ofCycle certificate⟩
  · rintro ⟨certificate⟩
    exact ⟨{
      vertex := certificate.dart.fst
      walk := certificate.cycle
      isCycle := certificate.cycle_isCycle
      length_ok := by
        rw [certificate.cycle_length]
        exact certificate.length_ok
    }⟩

/-- Set-membership form of an accepted edge-rooted return. -/
theorem hasEdgeRootedReturn_iff_exists_mem_returnLengthSet
    (object : FiniteObject.{u}) (ReturnLengthOK : Nat → Prop) :
    HasEdgeRootedReturn object ReturnLengthOK ↔
      ∃ dart : object.graph.Dart,
        ∃ length ∈ returnLengthSet object dart, ReturnLengthOK length := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.dart, certificate.path.length,
      ⟨certificate.path, certificate.isPath, rfl⟩,
      certificate.length_ok⟩
  · rintro ⟨dart, length, ⟨path, isPath, pathLength⟩, lengthOK⟩
    refine ⟨⟨dart, path, isPath, ?_⟩⟩
    rw [pathLength]
    exact lengthOK

/-- Exact target-avoidance algebra: every dart's explicit return-length set
is disjoint from the shifted accepted cycle lengths. -/
theorem not_hasCycleWithLength_iff_returnLengthSets_disjoint
    (CycleLengthOK : Nat → Prop) (object : FiniteObject.{u}) :
    ¬ HasCycleWithLength CycleLengthOK object ↔
      ∀ dart : object.graph.Dart,
        Disjoint (returnLengthSet object dart)
          (shiftedAcceptedSet CycleLengthOK) := by
  rw [hasCycleWithLength_iff_hasEdgeRootedReturn]
  rw [hasEdgeRootedReturn_iff_exists_mem_returnLengthSet]
  constructor
  · intro noReturn dart
    rw [Set.disjoint_left]
    intro length inReturn lengthAccepted
    exact noReturn ⟨dart, length, inReturn, lengthAccepted⟩
  · intro disjoint hasReturn
    obtain ⟨dart, length, inReturn, lengthAccepted⟩ := hasReturn
    exact (Set.disjoint_left.mp (disjoint dart)) inReturn lengthAccepted

/-- Minimal application profile for a named return predicate. Applications
supply only its equivalence to the successor-shift of `CycleLengthOK`. -/
structure RootedReturnTargetAlgebra (CycleLengthOK : Nat → Prop) where
  ReturnLengthOK : Nat → Prop
  returnLengthOK_iff_shifted : ∀ length,
    ReturnLengthOK length ↔ ShiftedCycleLength CycleLengthOK length

namespace RootedReturnTargetAlgebra

variable {CycleLengthOK : Nat → Prop}

/-- Canonical profile using the derived shifted predicate itself. -/
def shifted (CycleLengthOK : Nat → Prop) :
    RootedReturnTargetAlgebra CycleLengthOK where
  ReturnLengthOK := ShiftedCycleLength CycleLengthOK
  returnLengthOK_iff_shifted := fun _length => Iff.rfl

/-- The profile's proof-carrying return certificate. -/
abbrev RootedReturn (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u}) :=
  EdgeRootedReturn object profile.ReturnLengthOK

/-- Existence of one return accepted by the profile's named predicate. -/
abbrev HasRootedReturn (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u}) :=
  HasEdgeRootedReturn object profile.ReturnLengthOK

/-- A profile's named return predicate gives exactly the public cycle target. -/
theorem target_iff_hasRootedReturn
    (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u}) :
    HasCycleWithLength CycleLengthOK object ↔ profile.HasRootedReturn object := by
  rw [hasCycleWithLength_iff_hasEdgeRootedReturn]
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.mapLengthPredicate fun length accepted =>
      (profile.returnLengthOK_iff_shifted length).mpr accepted⟩
  · rintro ⟨certificate⟩
    exact ⟨certificate.mapLengthPredicate fun length accepted =>
      (profile.returnLengthOK_iff_shifted length).mp accepted⟩

/-- The profile form of target avoidance, stated against its named accepted
return-length set. -/
theorem not_target_iff_returnLengthSets_disjoint
    (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u}) :
    ¬ HasCycleWithLength CycleLengthOK object ↔
      ∀ dart : object.graph.Dart,
        Disjoint (returnLengthSet object dart)
          {length | profile.ReturnLengthOK length} := by
  rw [profile.target_iff_hasRootedReturn]
  change (¬ HasEdgeRootedReturn object profile.ReturnLengthOK) ↔ _
  rw [hasEdgeRootedReturn_iff_exists_mem_returnLengthSet]
  constructor
  · intro noReturn dart
    rw [Set.disjoint_left]
    intro length inReturn lengthAccepted
    exact noReturn ⟨dart, length, inReturn, lengthAccepted⟩
  · intro disjoint hasReturn
    obtain ⟨dart, length, inReturn, lengthAccepted⟩ := hasReturn
    exact (Set.disjoint_left.mp (disjoint dart)) inReturn lengthAccepted

/-- Framework-owned evidence that one graph avoids every return accepted by
the profile.  The target/return equivalence itself remains available from the
profile and is not copied into this payload. -/
structure AvoidanceCertificate
    (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u}) : Prop where
  returnLengthSetsDisjoint : ∀ dart : object.graph.Dart,
    Disjoint (returnLengthSet object dart)
      {length | profile.ReturnLengthOK length}

/-- Derive exact rooted-return avoidance from target avoidance. -/
def avoidanceCertificate
    (profile : RootedReturnTargetAlgebra CycleLengthOK)
    (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength CycleLengthOK object) :
    profile.AvoidanceCertificate object where
  returnLengthSetsDisjoint :=
    (profile.not_target_iff_returnLengthSets_disjoint object).mp avoids

/-- A rooted-return avoidance certificate recovers public target avoidance. -/
theorem AvoidanceCertificate.notTarget
    {profile : RootedReturnTargetAlgebra CycleLengthOK}
    {object : FiniteObject.{u}}
    (certificate : profile.AvoidanceCertificate object) :
    ¬ HasCycleWithLength CycleLengthOK object :=
  (profile.not_target_iff_returnLengthSets_disjoint object).mpr
    certificate.returnLengthSetsDisjoint

end RootedReturnTargetAlgebra

end Hypostructure.Graph
