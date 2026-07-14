import Mathlib.Tactic
import StructuralExhaustion.Graph.CycleCertificate
import StructuralExhaustion.Graph.InducedPathBridge
import StructuralExhaustion.Graph.MinimumDegreeCycle

namespace StructuralExhaustion.Graph.FanWindowCycle

open StructuralExhaustion

universe u uBranch

/-!
# Direct cycle elimination for two attachments in one path window

The data below are the literal graph hypotheses of a closed fan-window pair.
Every failed arithmetic safety clause is converted to a Mathlib simple-cycle
certificate.  CT1 then validates that explicit certificate or validates the
target-avoiding branch.  No walk universe or ambient graph family is searched.
-/

/-- Two ordered attachment positions of one external vertex. -/
structure ClosedAttachment {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) (outside : V) where
  first : Fin order
  second : Fin order
  first_lt_second : first < second
  outsidePath : ∀ position : Fin order, outside ≠ path position
  firstAdjacent : G.Adj outside (path first)
  secondAdjacent : G.Adj outside (path second)

namespace ClosedAttachment

def endpoint {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G} {outside : V}
    (attachment : ClosedAttachment path outside) (side : Bool) : Fin order :=
  if side then attachment.second else attachment.first

theorem endpoint_adjacent {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G} {outside : V}
    (attachment : ClosedAttachment path outside) (side : Bool) :
    G.Adj outside (path (attachment.endpoint side)) := by
  cases side <;> simp [endpoint, attachment.firstAdjacent,
    attachment.secondAdjacent]

end ClosedAttachment

/-- The exact graph data for two distinct neighbours of one external centre,
both closed on the same induced-path window. -/
structure ClosedPair {V : Type u} {G : SimpleGraph V} {order : Nat}
    (path : SimpleGraph.pathGraph order ↪g G) where
  center : V
  leftVertex : V
  rightVertex : V
  centerPath : ∀ position : Fin order, center ≠ path position
  distinct : leftVertex ≠ rightVertex
  centerLeft : G.Adj center leftVertex
  centerRight : G.Adj center rightVertex
  left : ClosedAttachment path leftVertex
  right : ClosedAttachment path rightVertex

/-- One exact failure of the direct-cycle-free arithmetic conditions. -/
inductive Violation {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G}
    (LengthOK : Nat → Prop) (pair : ClosedPair path) : Type u where
  | leftInternal
      (accepted : LengthOK
        (InducedPathAttachment.pairCycleLength pair.left.first
          pair.left.second))
  | rightInternal
      (accepted : LengthOK
        (InducedPathAttachment.pairCycleLength pair.right.first
          pair.right.second))
  | cross (leftSide rightSide : Bool)
      (accepted : LengthOK
        (4 + InducedPathAttachment.positionDistance
          (pair.left.endpoint leftSide) (pair.right.endpoint rightSide)))
  | interlaceLeft
      (first_lt_second : pair.left.first < pair.right.first)
      (second_lt_third : pair.right.first < pair.left.second)
      (third_lt_fourth : pair.left.second < pair.right.second)
      (accepted : LengthOK
        (4 + (pair.right.first.1 - pair.left.first.1) +
          (pair.right.second.1 - pair.left.second.1)))
  | interlaceRight
      (first_lt_second : pair.right.first < pair.left.first)
      (second_lt_third : pair.left.first < pair.right.second)
      (third_lt_fourth : pair.right.second < pair.left.second)
      (accepted : LengthOK
        (4 + (pair.left.first.1 - pair.right.first.1) +
          (pair.left.second.1 - pair.right.second.1)))

/-- Direct-cycle-free means precisely that none of the finite local failure
certificates exists. -/
def DirectCycleFree {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G}
    (LengthOK : Nat → Prop) (pair : ClosedPair path) : Prop :=
  ¬Nonempty (Violation LengthOK pair)

/-- Expanded arithmetic form of `DirectCycleFree`. -/
theorem directCycleFree_iff {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G}
    (LengthOK : Nat → Prop) (pair : ClosedPair path) :
    DirectCycleFree LengthOK pair ↔
      ¬LengthOK (InducedPathAttachment.pairCycleLength pair.left.first
        pair.left.second) ∧
      ¬LengthOK (InducedPathAttachment.pairCycleLength pair.right.first
        pair.right.second) ∧
      (∀ leftSide rightSide,
        ¬LengthOK (4 + InducedPathAttachment.positionDistance
          (pair.left.endpoint leftSide) (pair.right.endpoint rightSide))) ∧
      (pair.left.first < pair.right.first →
        pair.right.first < pair.left.second →
        pair.left.second < pair.right.second →
        ¬LengthOK (4 + (pair.right.first.1 - pair.left.first.1) +
          (pair.right.second.1 - pair.left.second.1))) ∧
      (pair.right.first < pair.left.first →
        pair.left.first < pair.right.second →
        pair.right.second < pair.left.second →
        ¬LengthOK (4 + (pair.left.first.1 - pair.right.first.1) +
          (pair.left.second.1 - pair.right.second.1))) := by
  constructor
  · intro free
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun accepted => free ⟨.leftInternal accepted⟩
    · exact fun accepted => free ⟨.rightInternal accepted⟩
    · exact fun leftSide rightSide accepted =>
        free ⟨.cross leftSide rightSide accepted⟩
    · exact fun h₁ h₂ h₃ accepted =>
        free ⟨.interlaceLeft h₁ h₂ h₃ accepted⟩
    · exact fun h₁ h₂ h₃ accepted =>
        free ⟨.interlaceRight h₁ h₂ h₃ accepted⟩
  · rintro ⟨leftSafe, rightSafe, crossSafe, interlaceLeftSafe,
      interlaceRightSafe⟩ ⟨violation⟩
    cases violation with
    | leftInternal accepted => exact leftSafe accepted
    | rightInternal accepted => exact rightSafe accepted
    | cross leftSide rightSide accepted =>
        exact crossSafe leftSide rightSide accepted
    | interlaceLeft h₁ h₂ h₃ accepted =>
        exact interlaceLeftSafe h₁ h₂ h₃ accepted
    | interlaceRight h₁ h₂ h₃ accepted =>
        exact interlaceRightSafe h₁ h₂ h₃ accepted

/-- Every exact arithmetic violation produces the corresponding literal
simple cycle. -/
def cycleOfViolation {V : Type u} {G : SimpleGraph V} {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g G}
    (LengthOK : Nat → Prop) (pair : ClosedPair path)
    (violation : Violation LengthOK pair) : CycleWithLength G LengthOK := by
  cases violation with
  | leftInternal accepted =>
      exact InducedPathAttachment.cycleOfAttachments LengthOK path
        pair.leftVertex pair.left.outsidePath pair.left.first pair.left.second
        pair.left.first_lt_second pair.left.firstAdjacent
        pair.left.secondAdjacent accepted
  | rightInternal accepted =>
      exact InducedPathAttachment.cycleOfAttachments LengthOK path
        pair.rightVertex pair.right.outsidePath pair.right.first
        pair.right.second pair.right.first_lt_second pair.right.firstAdjacent
        pair.right.secondAdjacent accepted
  | cross leftSide rightSide accepted =>
      let leftPosition := pair.left.endpoint leftSide
      let rightPosition := pair.right.endpoint rightSide
      by_cases positions : leftPosition ≤ rightPosition
      · apply InducedPathBridge.connectorCycle LengthOK path pair.rightVertex
          pair.center pair.leftVertex pair.right.outsidePath pair.centerPath
          pair.left.outsidePath pair.distinct.symm pair.centerRight.symm
          pair.centerLeft leftPosition rightPosition positions
          (pair.left.endpoint_adjacent leftSide)
          (pair.right.endpoint_adjacent rightSide)
        have valueOrder : leftPosition.1 ≤ rightPosition.1 := positions
        simpa [leftPosition, rightPosition,
          InducedPathAttachment.positionDistance, max_eq_right valueOrder,
          min_eq_left valueOrder] using accepted
      · have reverse : rightPosition ≤ leftPosition := by omega
        apply InducedPathBridge.connectorCycle LengthOK path pair.leftVertex
          pair.center pair.rightVertex pair.left.outsidePath pair.centerPath
          pair.right.outsidePath pair.distinct pair.centerLeft.symm
          pair.centerRight rightPosition leftPosition reverse
          (pair.right.endpoint_adjacent rightSide)
          (pair.left.endpoint_adjacent leftSide)
        have valueOrder : rightPosition.1 ≤ leftPosition.1 := reverse
        simpa [leftPosition, rightPosition,
          InducedPathAttachment.positionDistance, max_eq_left valueOrder,
          min_eq_right valueOrder] using accepted
  | interlaceLeft first_lt_second second_lt_third third_lt_fourth accepted =>
      exact InducedPathBridge.interlacingCycle LengthOK path pair.leftVertex
        pair.rightVertex pair.left.outsidePath pair.right.outsidePath
        pair.distinct pair.left.first pair.right.first pair.left.second
        pair.right.second first_lt_second second_lt_third third_lt_fourth
        pair.left.firstAdjacent pair.right.firstAdjacent
        pair.left.secondAdjacent pair.right.secondAdjacent accepted
  | interlaceRight first_lt_second second_lt_third third_lt_fourth accepted =>
      exact InducedPathBridge.interlacingCycle LengthOK path pair.rightVertex
        pair.leftVertex pair.right.outsidePath pair.left.outsidePath
        pair.distinct.symm pair.right.first pair.left.first pair.right.second
        pair.left.second first_lt_second second_lt_third third_lt_fourth
        pair.right.firstAdjacent pair.left.firstAdjacent
        pair.right.secondAdjacent pair.left.secondAdjacent accepted

/-! ## Certificate-driven CT1 execution -/

def encoding {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState) :=
  cycleTargetCertificateEncoding (P := base.problem) (fun object => object)
    base.LengthOK

def input {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object) :
    CT1.Input base.problem where
  context := ⟨object, baseline, state⟩

def runViolation
    {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    {order : Nat} (path : SimpleGraph.pathGraph order ↪g object.graph)
    (pair : ClosedPair path) (violation : Violation base.LengthOK pair) :=
  (encoding base).run (input base object baseline state)
    (cycleOfViolation base.LengthOK pair violation) trivial

def runAvoiding
    {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) :=
  (encoding base).runAvoiding (input base object baseline state) avoids

theorem directCycleFree_of_avoids
    {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK)
    {order : Nat} {path : SimpleGraph.pathGraph order ↪g object.graph}
    (pair : ClosedPair path) : DirectCycleFree base.LengthOK pair := by
  rintro ⟨violation⟩
  exact avoids ⟨cycleOfViolation base.LengthOK pair violation⟩

/-- Complete zero-enumeration CT1 avoiding stage and all direct arithmetic
consequences for closed pairs in the same window. -/
structure VerifiedAvoidingStage
    {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) : Prop where
  terminal : (runAvoiding base object baseline state avoids).result.terminal =
    .avoiding
  trace : (runAvoiding base object baseline state avoids).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal]
  checks : (runAvoiding base object baseline state avoids).checks = 0
  total : ∃ run : CT1.CertifiedAvoidingRun (encoding base).spec
      (input base object baseline state),
    run.result.terminal = .avoiding ∧
      run.result.trace = [.entry, .equivalenceCertification,
        .realizationDecision, .avoidingTerminal]
  directFree : ∀ {order : Nat}
    {path : SimpleGraph.pathGraph order ↪g object.graph}
    (pair : ClosedPair path), DirectCycleFree base.LengthOK pair

def verifiedAvoidingStage
    {BranchState : FiniteObject V → Type uBranch}
    (base : MinimumDegreeCycle.StaticInput V BranchState)
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (state : BranchState object)
    (avoids : ¬HasCycleWithLength object.graph base.LengthOK) :
    VerifiedAvoidingStage base object baseline state avoids where
  terminal := (runAvoiding base object baseline state avoids).terminal_eq
  trace := (runAvoiding base object baseline state avoids).trace_eq
  checks := (runAvoiding base object baseline state avoids).checks_eq
  total := ⟨runAvoiding base object baseline state avoids,
    (runAvoiding base object baseline state avoids).terminal_eq,
    (runAvoiding base object baseline state avoids).trace_eq⟩
  directFree := directCycleFree_of_avoids base object avoids

end StructuralExhaustion.Graph.FanWindowCycle
