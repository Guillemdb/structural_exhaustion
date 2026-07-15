import Mathlib.Tactic
import StructuralExhaustion.Graph.PackedBridgeReduction
import StructuralExhaustion.Graph.OpenPortSuppression
import StructuralExhaustion.Graph.SurplusPortActivity
import StructuralExhaustion.Graph.TriangularPortReturn

namespace StructuralExhaustion.Graph.SurplusPortActivation

open StructuralExhaustion
open scoped Sym2

universe u

/-!
# Canonical activation of degree-surplus ports

This layer joins the actual CT6 active-ledger residual to the local response
data attached to every surplus slot.  A slot is activated independently of
all other slots.  Its root return is obtained from the already verified CT2
bridgelessness stage, and its open or triangular response is selected by the
literal shoulder-chord test.

The activated schedule is the declared surplus-slot order.  It is not a path,
subgraph, or graph enumeration: its length is proved equal to the total stored
in the CT6 residual.
-/

/-- Common verified hypotheses for the activation stage on one packed minimal
counterexample.  The threshold equation is explicit because surplus slots are
the units above the cubic baseline. -/
structure Setup (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  minimumDegree_eq_three : input.minimumDegree = 3
  fourFree : ¬HasCycleWithLength ctx.G.object.graph HighCenterStructure.FourLength

namespace Setup

variable {input : PackedMinimumDegreeCycle.StaticInput}
  {ctx : Core.MinimalCounterexampleContext input.problem input.Target}

abbrev base (_setup : Setup input ctx) := input.fixed ctx.G.Vertex

def baseline (setup : Setup input ctx) :
    setup.base.problem.Baseline ctx.G.object :=
  (input.fixedContext ctx).baseline

/-- Deletion criticality, transported from the actual packed minimal context
and normalized by the cubic threshold equation. -/
theorem deletionCritical (setup : Setup input ctx) :
    ∀ dart : ctx.G.object.graph.Dart,
      ctx.G.object.degree dart.fst = 3 ∨
        ctx.G.object.degree dart.snd = 3 := by
  intro dart
  have tight := (input.fixed ctx.G.Vertex).dart_has_tight_endpoint
    (input.fixedContext ctx) dart
  change ctx.G.object.degree dart.fst = input.minimumDegree ∨
    ctx.G.object.degree dart.snd = input.minimumDegree at tight
  rwa [setup.minimumDegree_eq_three] at tight

theorem twoLeMinimum (setup : Setup input ctx) : 2 ≤ input.minimumDegree := by
  rw [setup.minimumDegree_eq_three]
  norm_num

def bridgeStage (setup : Setup input ctx) :
    input.BridgeReductionStage setup.twoLeMinimum ctx :=
  input.bridgeReductionStage setup.twoLeMinimum ctx

end Setup

abbrev Slot {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (_setup : Setup input ctx) :=
  SurplusPortActivity.ExcessPortSlot ctx.G.object

/-- The three manuscript roles in the bounded port support `T(p)`.  Keeping
the role in the type is essential for blocker `(c)`: equal carrier vertices
with different roles remain different blocker values. -/
inductive PortRole where
  | leftShoulder
  | rightShoulder
  | buffer
  deriving DecidableEq, Repr

/-- The vertex occupying one exact role in `T(p)`. -/
def portVertex {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) : PortRole → ctx.G.Vertex
  | .leftShoulder =>
      SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical
  | .rightShoulder =>
      SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical
  | .buffer => SurplusPortActivity.portEndpoint ctx.G.object slot

/-- The fixed three-role schedule; it is independent of the ambient graph. -/
def portRoles : List PortRole :=
  [.leftShoulder, .rightShoulder, .buffer]

@[simp] theorem portRoles_length : portRoles.length = 3 := rfl

theorem mem_portRoles (role : PortRole) : role ∈ portRoles := by
  cases role <;> simp [portRoles]

/-- The exact local support `T(p)={x,a_p,b_p}` of one selected surplus port. -/
def PortSupport {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact {
    SurplusPortActivity.portEndpoint ctx.G.object slot,
    SurplusPortActivity.firstShoulder ctx.G.object slot setup.deletionCritical,
    SurplusPortActivity.secondShoulder ctx.G.object slot setup.deletionCritical }

theorem portVertex_mem_portSupport {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) (role : PortRole) :
    portVertex setup slot role ∈ PortSupport setup slot := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  cases role <;> simp [portVertex, PortSupport]

theorem mem_portSupport_iff {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) (vertex : ctx.G.Vertex) :
    vertex ∈ PortSupport setup slot ↔
      vertex = SurplusPortActivity.portEndpoint ctx.G.object slot ∨
      vertex = SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical ∨
      vertex = SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  simp [PortSupport]

theorem portSupport_card {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) :
    (PortSupport setup slot).card = 3 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have firstNeSecond := HighCenterPort.firstShoulder_ne_secondShoulder
    ctx.G.object slot.1 (SurplusPortActivity.portCenter_high ctx.G.object slot)
    setup.deletionCritical (SurplusPortActivity.portOfSlot ctx.G.object slot)
  have firstAdjEndpoint := HighCenterPort.firstShoulder_adjacent_endpoint
    ctx.G.object slot.1 (SurplusPortActivity.portCenter_high ctx.G.object slot)
    setup.deletionCritical (SurplusPortActivity.portOfSlot ctx.G.object slot)
  have secondAdjEndpoint := HighCenterPort.secondShoulder_adjacent_endpoint
    ctx.G.object slot.1 (SurplusPortActivity.portCenter_high ctx.G.object slot)
    setup.deletionCritical (SurplusPortActivity.portOfSlot ctx.G.object slot)
  have xNeFirst : SurplusPortActivity.portEndpoint ctx.G.object slot ≠
      SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical := by
    exact firstAdjEndpoint.ne.symm
  have xNeSecond : SurplusPortActivity.portEndpoint ctx.G.object slot ≠
      SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical := by
    exact secondAdjEndpoint.ne.symm
  have firstNeSecond' :
      SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical ≠
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical :=
    firstNeSecond
  change ({SurplusPortActivity.portEndpoint ctx.G.object slot,
    SurplusPortActivity.firstShoulder ctx.G.object slot setup.deletionCritical,
    SurplusPortActivity.secondShoulder ctx.G.object slot
      setup.deletionCritical} : Finset ctx.G.Vertex).card = 3
  simp [xNeFirst, xNeSecond, firstNeSecond']

/-- The oriented centre-to-cubic-endpoint dart of a surplus slot. -/
def rootDart {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) : ctx.G.object.graph.Dart :=
  ⟨(slot.1, SurplusPortActivity.portEndpoint ctx.G.object slot),
    SurplusPortActivity.portEndpoint_adjacent ctx.G.object slot⟩

/-- The canonical proof-level return `R_p`, obtained from the reusable CT2
bridgelessness output.  It is one local choice from a proved reachability fact
and performs no path search. -/
noncomputable def rootReturn {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) :
    DartReturn ctx.G.object.graph (rootDart setup slot) :=
  setup.bridgeStage.dartReturn (rootDart setup slot)

/-- The first edge of `R_p` leaves the cubic endpoint through exactly one of
the two declared shoulders. -/
theorem rootReturn_firstShoulder {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) :
    (rootReturn setup slot).path.snd =
        SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical ∨
      (rootReturn setup slot).path.snd =
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical := by
  let root := rootReturn setup slot
  have notNil : ¬root.path.Nil :=
    root.path.not_nil_of_ne (rootDart setup slot).snd_ne_fst
  have deletedAdjacent := root.path.adj_snd notNil
  have ambientAdjacent : ctx.G.object.graph.Adj
      (SurplusPortActivity.portEndpoint ctx.G.object slot) root.path.snd :=
    (ctx.G.object.graph.deleteEdges_le {(rootDart setup slot).edge})
      deletedAdjacent
  have firstNeCenter : root.path.snd ≠ slot.1 := by
    intro firstEq
    have deleted := (SimpleGraph.deleteEdges_adj.mp deletedAdjacent).2
    apply deleted
    simp only [Set.mem_singleton_iff]
    change s(SurplusPortActivity.portEndpoint ctx.G.object slot,
      root.path.snd) =
      s(slot.1, SurplusPortActivity.portEndpoint ctx.G.object slot)
    rw [firstEq]
    exact Sym2.eq_swap
  have member := HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
    ctx.G.object slot.1 (SurplusPortActivity.portOfSlot ctx.G.object slot)
    ambientAdjacent firstNeCenter
  exact HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
    ctx.G.object slot.1 (SurplusPortActivity.portCenter_high ctx.G.object slot)
    setup.deletionCritical (SurplusPortActivity.portOfSlot ctx.G.object slot)
    member

/-- Exact response contract for an open port.  The path is a simple
shoulder-to-shoulder path in `G-x`, and its successor length is accepted by
the ambient target predicate. -/
structure OpenResponse {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open) where
  path : ctx.G.object.graph.Walk
    (SurplusPortActivity.firstShoulder ctx.G.object slot
      setup.deletionCritical)
    (SurplusPortActivity.secondShoulder ctx.G.object slot
      setup.deletionCritical)
  pathIsSimple : path.IsPath
  avoidsEndpoint : SurplusPortActivity.portEndpoint ctx.G.object slot ∉
    path.support
  predecessorAccepted : input.LengthOK (path.length + 1)

/-- Local suppression input extracted from one open surplus slot. -/
def openSuppressionSetup {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open) :
    OpenPortSuppression.Setup ctx.G.object where
  center := slot.1
  endpoint := SurplusPortActivity.portEndpoint ctx.G.object slot
  first := SurplusPortActivity.firstShoulder ctx.G.object slot
    setup.deletionCritical
  second := SurplusPortActivity.secondShoulder ctx.G.object slot
    setup.deletionCritical
  endpoint_ne_center :=
    (SurplusPortActivity.portEndpoint_adjacent ctx.G.object slot).ne.symm
  endpoint_ne_first :=
    (HighCenterPort.firstShoulder_adjacent_endpoint ctx.G.object slot.1
      (SurplusPortActivity.portCenter_high ctx.G.object slot)
      setup.deletionCritical
      (SurplusPortActivity.portOfSlot ctx.G.object slot)).ne.symm
  endpoint_ne_second :=
    (HighCenterPort.secondShoulder_adjacent_endpoint ctx.G.object slot.1
      (SurplusPortActivity.portCenter_high ctx.G.object slot)
      setup.deletionCritical
      (SurplusPortActivity.portOfSlot ctx.G.object slot)).ne.symm
  first_ne_second := HighCenterPort.firstShoulder_ne_secondShoulder
    ctx.G.object slot.1 (SurplusPortActivity.portCenter_high ctx.G.object slot)
    setup.deletionCritical (SurplusPortActivity.portOfSlot ctx.G.object slot)
  center_ne_first :=
    (HighCenterPort.ne_center_of_mem_shoulders ctx.G.object slot.1
      (SurplusPortActivity.portOfSlot ctx.G.object slot)
      (HighCenterPort.firstShoulder_mem ctx.G.object slot.1
        (SurplusPortActivity.portCenter_high ctx.G.object slot)
        setup.deletionCritical
        (SurplusPortActivity.portOfSlot ctx.G.object slot))).symm
  center_ne_second :=
    (HighCenterPort.ne_center_of_mem_shoulders ctx.G.object slot.1
      (SurplusPortActivity.portOfSlot ctx.G.object slot)
      (HighCenterPort.secondShoulder_mem ctx.G.object slot.1
        (SurplusPortActivity.portCenter_high ctx.G.object slot)
        setup.deletionCritical
        (SurplusPortActivity.portOfSlot ctx.G.object slot))).symm
  endpoint_neighbors := by
    intro vertex
    constructor
    · intro adjacent
      by_cases central : vertex = slot.1
      · exact Or.inl central
      · have member :=
          HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
            ctx.G.object slot.1
            (SurplusPortActivity.portOfSlot ctx.G.object slot)
            adjacent central
        have sides :=
          HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
            ctx.G.object slot.1
            (SurplusPortActivity.portCenter_high ctx.G.object slot)
            setup.deletionCritical
            (SurplusPortActivity.portOfSlot ctx.G.object slot) member
        exact Or.inr sides
    · rintro (rfl | rfl | rfl)
      · exact (SurplusPortActivity.portEndpoint_adjacent
          ctx.G.object slot).symm
      · exact (HighCenterPort.firstShoulder_adjacent_endpoint
          ctx.G.object slot.1
          (SurplusPortActivity.portCenter_high ctx.G.object slot)
          setup.deletionCritical
          (SurplusPortActivity.portOfSlot ctx.G.object slot)).symm
      · exact (HighCenterPort.secondShoulder_adjacent_endpoint
          ctx.G.object slot.1
          (SurplusPortActivity.portCenter_high ctx.G.object slot)
          setup.deletionCritical
          (SurplusPortActivity.portOfSlot ctx.G.object slot)).symm
  open_shoulders := by
    intro adjacent
    letI : DecidableRel ctx.G.object.graph.Adj :=
      ctx.G.object.input.decideAdj
    change (if ctx.G.object.graph.Adj
      (SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical)
      (SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical)
      then HighCenterPort.PortType.triangular
      else HighCenterPort.PortType.open) =
        HighCenterPort.PortType.open at isOpen
    simp [adjacent] at isOpen
  center_high := SurplusPortActivity.portCenter_high ctx.G.object slot

/-- The open response is forced locally by suppressing the cubic endpoint and
applying packed minimality.  This discharges the open-response input of the
activation constructor; it is not an additional hypothesis. -/
noncomputable def openResponseFromMinimality
    {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open) :
    OpenResponse setup slot isOpen := by
  let suppression := openSuppressionSetup setup slot isOpen
  let witness := Classical.choice
    (OpenPortSuppression.Setup.witnessFromMinimality input ctx suppression
      setup.minimumDegree_eq_three)
  exact {
    path := witness.path
    pathIsSimple := witness.isPath
    avoidsEndpoint := witness.endpoint_not_mem
    predecessorAccepted := witness.predecessor_length
  }

/-- Triangular-port setup specialized to one surplus slot. -/
def triangularSetup {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) :
    TriangularPortReturn.Setup setup.base ctx.G.object setup.baseline slot.1 where
  centerHigh := SurplusPortActivity.portCenter_high ctx.G.object slot
  threeLeMinimum := by
    change 3 ≤ input.minimumDegree
    rw [setup.minimumDegree_eq_three]
  deletionCritical := setup.deletionCritical
  fourFree := setup.fourFree

/-- A triangular surplus slot as the exact port index consumed by the
reusable triangular-return profile. -/
def triangularPort {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    TriangularPortReturn.TriPort (triangularSetup setup slot) :=
  ⟨SurplusPortActivity.portOfSlot ctx.G.object slot, isTriangular⟩

/-- The existing CT1 triangular-return stage instantiated on the same root
return used by the active demand. -/
noncomputable def triangularReturnStage
    {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    TriangularPortReturn.VerifiedStage
      (triangularSetup setup slot)
      (triangularPort setup slot isTriangular)
      (rootReturn setup slot)
      (input.fixedContext ctx).avoids :=
  TriangularPortReturn.verifiedStage
    (triangularSetup setup slot)
    (triangularPort setup slot isTriangular)
    (rootReturn setup slot)
    (input.fixedContext ctx).avoids

/-- The literal triangle `x-a_p-b_p-x` of a triangular port. -/
def triangle {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    ctx.G.object.graph.Walk
      (SurplusPortActivity.portEndpoint ctx.G.object slot)
      (SurplusPortActivity.portEndpoint ctx.G.object slot) := by
  let port := SurplusPortActivity.portOfSlot ctx.G.object slot
  let centerHigh := SurplusPortActivity.portCenter_high ctx.G.object slot
  have chord : ctx.G.object.graph.Adj
      (SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical)
      (SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical) := by
    exact HighCenterPort.shoulders_adjacent_of_triangular ctx.G.object slot.1
      centerHigh setup.deletionCritical port isTriangular
  exact .cons
    (HighCenterPort.firstShoulder_adjacent_endpoint ctx.G.object slot.1
      centerHigh setup.deletionCritical port).symm
    (.cons chord
      (.cons (HighCenterPort.secondShoulder_adjacent_endpoint ctx.G.object
        slot.1 centerHigh setup.deletionCritical port) .nil))

theorem triangle_length {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    (triangle setup slot isTriangular).length = 3 := by
  rfl

theorem triangle_isCycle {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    (triangle setup slot isTriangular).IsCycle := by
  let port := SurplusPortActivity.portOfSlot ctx.G.object slot
  let centerHigh := SurplusPortActivity.portCenter_high ctx.G.object slot
  have firstNeSecond := HighCenterPort.firstShoulder_ne_secondShoulder
    ctx.G.object slot.1 centerHigh setup.deletionCritical port
  have firstAdjEndpoint := HighCenterPort.firstShoulder_adjacent_endpoint
    ctx.G.object slot.1 centerHigh setup.deletionCritical port
  have secondAdjEndpoint := HighCenterPort.secondShoulder_adjacent_endpoint
    ctx.G.object slot.1 centerHigh setup.deletionCritical port
  have endpointNeFirst : SurplusPortActivity.portEndpoint ctx.G.object slot ≠
      SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical := firstAdjEndpoint.ne.symm
  have endpointNeSecond : SurplusPortActivity.portEndpoint ctx.G.object slot ≠
      SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical := secondAdjEndpoint.ne.symm
  have firstNeSecond' :
      SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical ≠
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical := firstNeSecond
  have firstNeEndpoint :
      SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical ≠
        SurplusPortActivity.portEndpoint ctx.G.object slot :=
    firstAdjEndpoint.ne
  have secondNeEndpoint :
      SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical ≠
        SurplusPortActivity.portEndpoint ctx.G.object slot :=
    secondAdjEndpoint.ne
  have rootNeChord :
      s(SurplusPortActivity.portEndpoint ctx.G.object slot,
          SurplusPortActivity.firstShoulder ctx.G.object slot
            setup.deletionCritical) ≠
        s(SurplusPortActivity.firstShoulder ctx.G.object slot
            setup.deletionCritical,
          SurplusPortActivity.secondShoulder ctx.G.object slot
            setup.deletionCritical) := by
    intro equal
    rcases Sym2.eq_iff.mp equal with ⟨endpointEq, _⟩ |
      ⟨endpointEq, _⟩
    · exact endpointNeFirst endpointEq
    · exact endpointNeSecond endpointEq
  have rootNeLast :
      s(SurplusPortActivity.portEndpoint ctx.G.object slot,
          SurplusPortActivity.firstShoulder ctx.G.object slot
            setup.deletionCritical) ≠
        s(SurplusPortActivity.secondShoulder ctx.G.object slot
            setup.deletionCritical,
          SurplusPortActivity.portEndpoint ctx.G.object slot) := by
    intro equal
    rcases Sym2.eq_iff.mp equal with ⟨endpointEq, _⟩ |
      ⟨_, shoulderEq⟩
    · exact endpointNeSecond endpointEq
    · exact firstNeSecond' shoulderEq
  have chordNeLast :
      s(SurplusPortActivity.firstShoulder ctx.G.object slot
            setup.deletionCritical,
          SurplusPortActivity.secondShoulder ctx.G.object slot
            setup.deletionCritical) ≠
        s(SurplusPortActivity.secondShoulder ctx.G.object slot
            setup.deletionCritical,
          SurplusPortActivity.portEndpoint ctx.G.object slot) := by
    intro equal
    rcases Sym2.eq_iff.mp equal with ⟨shoulderEq, _⟩ |
      ⟨endpointEq, _⟩
    · exact firstNeSecond' shoulderEq
    · exact firstNeEndpoint endpointEq
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    change [
      s(SurplusPortActivity.portEndpoint ctx.G.object slot,
        SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical),
      s(SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical,
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical),
      s(SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical,
        SurplusPortActivity.portEndpoint ctx.G.object slot)].Nodup
    simp [rootNeChord, rootNeLast, chordNeLast]
  · intro nilEq
    have lengthEq := congrArg SimpleGraph.Walk.length nilEq
    rw [triangle_length setup slot isTriangular] at lengthEq
    simp at lengthEq
  · simp only [triangle, SimpleGraph.Walk.support_cons, List.tail_cons]
    change [
      SurplusPortActivity.firstShoulder ctx.G.object slot
        setup.deletionCritical,
      SurplusPortActivity.secondShoulder ctx.G.object slot
        setup.deletionCritical,
      SurplusPortActivity.portEndpoint ctx.G.object slot].Nodup
    simp [firstNeSecond', firstNeEndpoint, secondNeEndpoint]

/-- The complete local response support of one activated demand.  Both
branches retain the same canonical root return. -/
inductive Response {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) where
  | open
      (isOpen : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot = .open)
      (response : OpenResponse setup slot isOpen)
  | triangular
      (isTriangular : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot = .triangular)
      (returnStage : TriangularPortReturn.VerifiedStage
        (triangularSetup setup slot)
        (triangularPort setup slot isTriangular)
        (rootReturn setup slot)
        (input.fixedContext ctx).avoids)

/-- One active surplus demand, with exact support, root return, and the
open/triangular response selected by the graph's computed port type. -/
structure ActiveDemand {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) (slot : Slot setup) where
  support : Finset ctx.G.Vertex := PortSupport setup slot
  support_eq : support = PortSupport setup slot := by rfl
  root : DartReturn ctx.G.object.graph (rootDart setup slot) :=
    rootReturn setup slot
  root_eq : root = rootReturn setup slot := by rfl
  response : Response setup slot

namespace ActiveDemand

variable {input : PackedMinimumDegreeCycle.StaticInput}
  {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
  {setup : Setup input ctx} {slot : Slot setup}

/-- Edge set of the canonical root return, viewed in the ambient graph.  A
deleted-edge walk has the same `Sym2` edge labels as its ambient image. -/
noncomputable def rootReturnEdges (setup : Setup input ctx)
    (slot : Slot setup) : Finset (Sym2 ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (Sym2 ctx.G.Vertex) := inferInstance
  exact (rootReturn setup slot).path.edges.toFinset

/-- Exact edge-labelled response support in the open branch: the root return,
the suppression path, and the two endpoint-to-shoulder incidences. -/
noncomputable def openGammaEdges
    (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open)
    (response : OpenResponse setup slot isOpen) :
    Finset (Sym2 ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (Sym2 ctx.G.Vertex) := inferInstance
  exact rootReturnEdges setup slot ∪
    response.path.edges.toFinset ∪
    {s(SurplusPortActivity.portEndpoint ctx.G.object slot,
        SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical),
      s(SurplusPortActivity.portEndpoint ctx.G.object slot,
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical)}

/-- Exact edge-labelled response support in the triangular branch: the root
return and the three literal edges of `x-a_p-b_p-x`. -/
noncomputable def triangularGammaEdges
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular) :
    Finset (Sym2 ctx.G.Vertex) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableEq (Sym2 ctx.G.Vertex) := inferInstance
  exact rootReturnEdges setup slot ∪
    (triangle setup slot isTriangular).edges.toFinset

/-- The exact response edge support `Γ(p)` selected by the response branch. -/
noncomputable def GammaEdges (demand : ActiveDemand setup slot) :
    Finset (Sym2 ctx.G.Vertex) :=
  match demand.response with
  | .open isOpen response => openGammaEdges isOpen response
  | .triangular isTriangular _returnStage =>
      triangularGammaEdges isTriangular

noncomputable abbrev responseEdges (demand : ActiveDemand setup slot) :=
  demand.GammaEdges

/-- Vertices incident with at least one edge of the exact response support.
This is derived from `GammaEdges`, not separately declared data. -/
noncomputable def GammaVertices (demand : ActiveDemand setup slot) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact demand.GammaEdges.biUnion Sym2.toFinset

theorem mem_GammaVertices_iff (demand : ActiveDemand setup slot)
    (vertex : ctx.G.Vertex) :
    vertex ∈ demand.GammaVertices ↔
      ∃ edge ∈ demand.GammaEdges, vertex ∈ edge := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  change vertex ∈ demand.GammaEdges.biUnion Sym2.toFinset ↔ _
  simp only [Finset.mem_biUnion, Sym2.mem_toFinset]

/-- Exact open-branch equation for the active demand's response support. -/
theorem gammaEdges_eq_open (demand : ActiveDemand setup slot)
    (isOpen : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open)
    (response : OpenResponse setup slot isOpen)
    (branch : demand.response = .open isOpen response) :
    demand.GammaEdges = openGammaEdges isOpen response := by
  simp only [GammaEdges, branch]

/-- Exact triangular-branch equation for the active demand's response
support. -/
theorem gammaEdges_eq_triangular (demand : ActiveDemand setup slot)
    (isTriangular : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .triangular)
    (returnStage : TriangularPortReturn.VerifiedStage
      (triangularSetup setup slot)
      (triangularPort setup slot isTriangular)
      (rootReturn setup slot)
      (input.fixedContext ctx).avoids)
    (branch : demand.response = .triangular isTriangular returnStage) :
    demand.GammaEdges = triangularGammaEdges isTriangular := by
  simp only [GammaEdges, branch]

end ActiveDemand

/-- Activate one slot using the open-port witness constructor only in the
open branch.  The triangular branch is entirely graph-derived. -/
noncomputable def activate {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx)
    (openResponse : ∀ (slot : Slot setup)
      (isOpen : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot = .open),
      OpenResponse setup slot isOpen)
    (slot : Slot setup) : ActiveDemand setup slot := by
  classical
  refine { response := ?_ }
  by_cases typeEq : SurplusPortActivity.portType ctx.G.object
      setup.deletionCritical slot = .open
  · exact .open typeEq (openResponse slot typeEq)
  · have triangularEq : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot = .triangular := by
      cases portTypeEq : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot
      · exact (typeEq portTypeEq).elim
      · rfl
    exact .triangular triangularEq
      (triangularReturnStage setup slot triangularEq)

/-- The activated schedule is the exact declared excess-slot order.  The CT6
residual is an explicit input, making the route dependence visible in the
type instead of silently rebuilding a global family. -/
def activatedSchedule {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx)
    (_residual : CT6.ActiveLedgerResidual
      (SurplusPortActivity.spec setup.base)
      (SurplusPortActivity.capability setup.base ctx.G.object)
      (SurplusPortActivity.context setup.base ctx.G.object setup.baseline)) :
    List (Slot setup) :=
  (SurplusPortActivity.portSlots ctx.G.object).orderedValues

/-- Exact cardinality of the activated schedule, read against the total in
the actual CT6 residual produced on this graph. -/
theorem activatedSchedule_length_eq_residualTotal
    {input : PackedMinimumDegreeCycle.StaticInput}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (setup : Setup input ctx) :
    (activatedSchedule setup
      (SurplusPortActivity.run setup.base ctx.G.object setup.baseline
        setup.deletionCritical).residual).length =
      (SurplusPortActivity.run setup.base ctx.G.object setup.baseline
        setup.deletionCritical).residual.total := by
  rw [SurplusPortActivity.run_total_eq_surplus setup.base ctx.G.object
    setup.baseline setup.deletionCritical]
  change (SurplusPortActivity.portSlots ctx.G.object).orderedValues.length = _
  rw [show (SurplusPortActivity.portSlots ctx.G.object).orderedValues.length =
      (SurplusPortActivity.portSlots ctx.G.object).card by
    simp [FinEnum.orderedValues, FinEnum.toList]]
  exact SurplusPortActivity.portSlots_card_eq_surplus ctx.G.object

/-- Full framework-owned CT6 activation output.  Every scheduled slot carries
its local active demand, and the schedule cardinality is the machine's actual
active-ledger total. -/
structure VerifiedActivatedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (setup : Setup input ctx) where
  run : CT6.ActiveLedgerRun
    (SurplusPortActivity.spec setup.base)
    (SurplusPortActivity.capability setup.base ctx.G.object)
    (SurplusPortActivity.context setup.base ctx.G.object setup.baseline) :=
      SurplusPortActivity.run setup.base ctx.G.object setup.baseline
        setup.deletionCritical
  run_eq : run = SurplusPortActivity.run setup.base ctx.G.object
    setup.baseline setup.deletionCritical := by rfl
  demand : ∀ slot : Slot setup, ActiveDemand setup slot
  scheduleLength : (activatedSchedule setup run.residual).length =
    run.residual.total
  supportCard : ∀ slot : Slot setup, (PortSupport setup slot).card = 3
  firstLanding : ∀ slot : Slot setup,
    (rootReturn setup slot).path.snd =
        SurplusPortActivity.firstShoulder ctx.G.object slot
          setup.deletionCritical ∨
      (rootReturn setup slot).path.snd =
        SurplusPortActivity.secondShoulder ctx.G.object slot
          setup.deletionCritical

noncomputable def verifiedActivatedStage
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (setup : Setup input ctx)
    (openResponse : ∀ (slot : Slot setup)
      (isOpen : SurplusPortActivity.portType ctx.G.object
        setup.deletionCritical slot = .open),
      OpenResponse setup slot isOpen) :
    VerifiedActivatedStage input ctx setup where
  demand := activate setup openResponse
  scheduleLength := activatedSchedule_length_eq_residualTotal setup
  supportCard := portSupport_card setup
  firstLanding := rootReturn_firstShoulder setup

/-- Unconditional activation on a packed cubic minimal counterexample.  Open
responses come from the suppression/minimality theorem and triangular
responses come from the triangular-return theorem. -/
noncomputable def verifiedActivatedStageFromMinimality
    (input : PackedMinimumDegreeCycle.StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (setup : Setup input ctx) :
    VerifiedActivatedStage input ctx setup :=
  verifiedActivatedStage input ctx setup
    (openResponseFromMinimality setup)

end StructuralExhaustion.Graph.SurplusPortActivation
