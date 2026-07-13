import Erdos64EG.InternalProblem
import StructuralExhaustion.Graph.EdgeRootedReturn

namespace Erdos64EG.Internal

open StructuralExhaustion.Graph

universe u

/-!
# Mersenne edge-rooted target algebra

The manuscript's return path is represented literally as a Mathlib simple
path in `G.deleteEdges {e}`.  Restoring the root edge and deleting the first
edge of a cycle are supplied by the reusable graph layer.
-/

/-- Executable Mersenne-length predicate.  Its successor is an accepted
power-of-two cycle length. -/
def MersenneLength (length : Nat) : Prop :=
  PowerOfTwoLength (length + 1)

instance mersenneLengthDecidable (length : Nat) :
    Decidable (MersenneLength length) :=
  powerOfTwoLengthDecidable (length + 1)

/-- The executable predicate is exactly the manuscript set
`{2^j - 1 | j ≥ 2}`. -/
theorem mersenneLength_iff (length : Nat) :
    MersenneLength length ↔
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent - 1 := by
  rw [MersenneLength, powerOfTwoLength_iff]
  constructor
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := pow_pos (by decide) exponent
    omega
  · rintro ⟨exponent, lower, equality⟩
    refine ⟨exponent, lower, ?_⟩
    have positive : 0 < 2 ^ exponent := pow_pos (by decide) exponent
    omega

/-- The manuscript's Mersenne set. -/
def MersenneSet : Set Nat := {length | MersenneLength length}

/-- One oriented edge with a simple Mersenne-length return in the graph with
that edge deleted. -/
abbrev MersenneReturn {V : Type u} (G : SimpleGraph V) :=
  EdgeRootedReturn G MersenneLength

abbrev HasMersenneReturn {V : Type u} (G : SimpleGraph V) :=
  HasEdgeRootedReturn G MersenneLength

/-- The return-length set `R_e(G)` from the manuscript. -/
def returnSet {V : Type u} (G : SimpleGraph V) (dart : G.Dart) : Set Nat :=
  edgeReturnSet G dart

/-- Fixed-exponent form of the root-edge dictionary. -/
theorem hasPowerCycle_iff_hasRootedReturn
    {V : Type u} (G : SimpleGraph V) (exponent : Nat)
    (_lower : 2 ≤ exponent) :
    HasCycleWithLength G (fun length => length = 2 ^ exponent) ↔
      HasEdgeRootedReturn G
        (fun length => length = 2 ^ exponent - 1) := by
  have positive : 0 < 2 ^ exponent := pow_pos (by decide) exponent
  constructor
  · intro hasCycle
    obtain ⟨certificate⟩ :=
      (hasCycleWithLength_iff_hasEdgeRootedReturn G
        (fun length => length = 2 ^ exponent)).mp hasCycle
    refine ⟨{
      dart := certificate.dart
      path := certificate.path
      isPath := certificate.isPath
      length_ok := ?_
    }⟩
    have successor := certificate.length_ok
    omega
  · rintro ⟨certificate⟩
    apply (hasCycleWithLength_iff_hasEdgeRootedReturn G
      (fun length => length = 2 ^ exponent)).mpr
    refine ⟨{
      dart := certificate.dart
      path := certificate.path
      isPath := certificate.isPath
      length_ok := ?_
    }⟩
    have predecessor := certificate.length_ok
    omega

/-- A power-of-two target cycle is equivalent to one edge-rooted Mersenne
return. -/
theorem target_iff_hasMersenneReturn {V : Type u} (object : Object V) :
    Target object ↔ HasMersenneReturn object.graph :=
  hasCycleWithLength_iff_hasEdgeRootedReturn object.graph PowerOfTwoLength

/-- Exact counterexample form of the target algebra: every oriented return
set is disjoint from the Mersenne set. -/
theorem not_target_iff_returnSets_disjoint {V : Type u}
    (object : Object V) :
    ¬ Target object ↔
      ∀ dart : object.graph.Dart,
        Disjoint (returnSet object.graph dart) MersenneSet := by
  simpa [Target, staticInput, MinimumDegreeCycle.StaticInput.Target,
    returnSet, MersenneSet, MersenneLength] using
    (noCycleWithLength_iff_returnSets_disjoint object.graph PowerOfTwoLength)

end Erdos64EG.Internal
