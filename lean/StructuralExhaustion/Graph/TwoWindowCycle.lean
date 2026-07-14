import Mathlib.Tactic
import StructuralExhaustion.Graph.FanWindowCycle

namespace StructuralExhaustion.Graph.TwoWindowCycle

open StructuralExhaustion

universe u uBranch

/-!
# Direct cycles through two vertex-disjoint induced windows

Two external vertices joined inside two vertex-disjoint induced paths give a
literal simple cycle.  The construction uses orientation-independent symbolic
bridges and does not enumerate paths, walks, vertex tuples, or ambient graphs.
-/

/-- Exact graph data used by the two-window direct-cycle lemma. -/
structure Data {V : Type u} {G : SimpleGraph V}
    {firstOrder secondOrder : Nat}
    (firstPath : SimpleGraph.pathGraph firstOrder ↪g G)
    (secondPath : SimpleGraph.pathGraph secondOrder ↪g G) where
  leftVertex : V
  rightVertex : V
  distinct : leftVertex ≠ rightVertex
  leftOutsideFirst : ∀ position, leftVertex ≠ firstPath position
  rightOutsideFirst : ∀ position, rightVertex ≠ firstPath position
  leftOutsideSecond : ∀ position, leftVertex ≠ secondPath position
  rightOutsideSecond : ∀ position, rightVertex ≠ secondPath position
  windowsDisjoint : ∀ firstPosition secondPosition,
    firstPath firstPosition ≠ secondPath secondPosition
  leftFirst : Fin firstOrder
  rightFirst : Fin firstOrder
  leftSecond : Fin secondOrder
  rightSecond : Fin secondOrder
  leftFirstAdjacent : G.Adj leftVertex (firstPath leftFirst)
  rightFirstAdjacent : G.Adj rightVertex (firstPath rightFirst)
  leftSecondAdjacent : G.Adj leftVertex (secondPath leftSecond)
  rightSecondAdjacent : G.Adj rightVertex (secondPath rightSecond)

/-- Sum of the two internal path-segment lengths. -/
def segmentTotal {V : Type u} {G : SimpleGraph V}
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g G}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g G}
    (data : Data firstPath secondPath) : Nat :=
  InducedPathAttachment.positionDistance data.leftFirst data.rightFirst +
    InducedPathAttachment.positionDistance data.leftSecond data.rightSecond

/-- Arithmetic condition excluding the direct two-window target cycle. -/
def DirectCycleFree {V : Type u} {G : SimpleGraph V}
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g G}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g G}
    (LengthOK : Nat → Prop) (data : Data firstPath secondPath) : Prop :=
  ¬LengthOK (4 + segmentTotal data)

/-- The two orientation-independent bridges form a literal simple cycle of
length `4 + segmentTotal data`. -/
def cycle {V : Type u} {G : SimpleGraph V}
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g G}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g G}
    (LengthOK : Nat → Prop) (data : Data firstPath secondPath)
    (accepted : LengthOK (4 + segmentTotal data)) :
    CycleWithLength G LengthOK := by
  let firstRoute := InducedPathBridge.unorderedBridge firstPath
    data.leftVertex data.rightVertex data.leftFirst data.rightFirst
    data.leftFirstAdjacent data.rightFirstAdjacent
  let secondRoute := InducedPathBridge.unorderedBridge secondPath
    data.rightVertex data.leftVertex data.rightSecond data.leftSecond
    data.rightSecondAdjacent data.leftSecondAdjacent
  have firstRoutePath : firstRoute.IsPath :=
    InducedPathBridge.unorderedBridge_isPath firstPath data.leftVertex
      data.rightVertex data.leftOutsideFirst data.rightOutsideFirst
      data.distinct data.leftFirst data.rightFirst data.leftFirstAdjacent
      data.rightFirstAdjacent
  have secondRoutePath : secondRoute.IsPath :=
    InducedPathBridge.unorderedBridge_isPath secondPath data.rightVertex
      data.leftVertex data.rightOutsideSecond data.leftOutsideSecond
      data.distinct.symm data.rightSecond data.leftSecond
      data.rightSecondAdjacent data.leftSecondAdjacent
  have disjoint : firstRoute.support.tail.Disjoint
      secondRoute.support.tail := by
    rw [List.disjoint_left]
    intro vertex firstMember secondMember
    rcases InducedPathBridge.unorderedBridge_tail_member firstPath
        data.leftVertex data.rightVertex data.leftOutsideFirst
        data.rightOutsideFirst data.distinct data.leftFirst data.rightFirst
        data.leftFirstAdjacent data.rightFirstAdjacent firstMember with
      ⟨firstPosition, firstEqual⟩ | firstRight
    · rcases InducedPathBridge.unorderedBridge_tail_member secondPath
          data.rightVertex data.leftVertex data.rightOutsideSecond
          data.leftOutsideSecond data.distinct.symm data.rightSecond
          data.leftSecond data.rightSecondAdjacent data.leftSecondAdjacent
          secondMember with
        ⟨secondPosition, secondEqual⟩ | secondRight
      · exact data.windowsDisjoint firstPosition secondPosition
          (firstEqual.trans secondEqual.symm)
      · exact data.leftOutsideFirst firstPosition
          (secondRight.symm.trans firstEqual.symm)
    · subst vertex
      rcases InducedPathBridge.unorderedBridge_tail_member secondPath
          data.rightVertex data.leftVertex data.rightOutsideSecond
          data.leftOutsideSecond data.distinct.symm data.rightSecond
          data.leftSecond data.rightSecondAdjacent data.leftSecondAdjacent
          secondMember with
        ⟨secondPosition, secondEqual⟩ | secondRight
      · exact data.rightOutsideSecond secondPosition secondEqual.symm
      · exact data.distinct secondRight.symm
  refine {
    vertex := data.leftVertex
    walk := firstRoute.append secondRoute
    isCycle := firstRoutePath.isCycle_append secondRoutePath disjoint
      (Or.inl ?_)
    length_ok := ?_
  }
  · rw [InducedPathBridge.unorderedBridge_length firstPath data.leftVertex
      data.rightVertex data.leftFirst data.rightFirst data.leftFirstAdjacent
      data.rightFirstAdjacent]
    omega
  · rw [SimpleGraph.Walk.length_append,
      InducedPathBridge.unorderedBridge_length firstPath data.leftVertex
        data.rightVertex data.leftFirst data.rightFirst data.leftFirstAdjacent
        data.rightFirstAdjacent,
      InducedPathBridge.unorderedBridge_length secondPath data.rightVertex
        data.leftVertex data.rightSecond data.leftSecond
        data.rightSecondAdjacent data.leftSecondAdjacent]
    simpa [segmentTotal, InducedPathAttachment.positionDistance,
      max_comm, min_comm, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using accepted

theorem directCycleFree_of_avoids
    {V : Type u} {G : SimpleGraph V}
    {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g G}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g G}
    (LengthOK : Nat → Prop) (avoids : ¬HasCycleWithLength G LengthOK)
    (data : Data firstPath secondPath) : DirectCycleFree LengthOK data := by
  intro accepted
  exact avoids ⟨cycle LengthOK data accepted⟩

/-- Complete CT1 avoiding stage for every pair of vertex-disjoint induced
windows in the retained branch context. -/
structure VerifiedAvoidingStage
    {V : Type u} {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) : Prop where
  terminal : (FanWindowCycle.runAvoiding base object baseline state
    avoids).result.terminal = .avoiding
  trace : (FanWindowCycle.runAvoiding base object baseline state
    avoids).result.trace = [.entry, .equivalenceCertification,
      .realizationDecision, .avoidingTerminal]
  checks : (FanWindowCycle.runAvoiding base object baseline state
    avoids).checks = 0
  total : ∃ run : CT1.CertifiedAvoidingRun (FanWindowCycle.encoding base).spec
      (FanWindowCycle.input base object baseline state),
    run.result.terminal = .avoiding ∧
      run.result.trace = [.entry, .equivalenceCertification,
        .realizationDecision, .avoidingTerminal]
  directFree : ∀ {firstOrder secondOrder : Nat}
    {firstPath : SimpleGraph.pathGraph firstOrder ↪g object.graph}
    {secondPath : SimpleGraph.pathGraph secondOrder ↪g object.graph}
    (data : Data firstPath secondPath), DirectCycleFree base.LengthOK data

def verifiedAvoidingStage
    {V : Type u} {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) :
    VerifiedAvoidingStage base object baseline state avoids where
  terminal := (FanWindowCycle.runAvoiding base object baseline state
    avoids).terminal_eq
  trace := (FanWindowCycle.runAvoiding base object baseline state
    avoids).trace_eq
  checks := (FanWindowCycle.runAvoiding base object baseline state
    avoids).checks_eq
  total := ⟨FanWindowCycle.runAvoiding base object baseline state avoids,
    (FanWindowCycle.runAvoiding base object baseline state avoids).terminal_eq,
    (FanWindowCycle.runAvoiding base object baseline state avoids).trace_eq⟩
  directFree := directCycleFree_of_avoids base.LengthOK avoids

end StructuralExhaustion.Graph.TwoWindowCycle
