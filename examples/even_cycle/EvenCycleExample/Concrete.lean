import EvenCycleExample.Run
import StructuralExhaustion.Graph.OpenPortCompatibility
import StructuralExhaustion.Graph.PortShoulderLedger
import StructuralExhaustion.Graph.SurplusPortActivity
import StructuralExhaustion.Graph.TriangularShoulderCompletion
import StructuralExhaustion.Graph.TriangularPortReturn
import StructuralExhaustion.Graph.TriangularFirstLanding
import StructuralExhaustion.Graph.TriangularCrossShoulder
import StructuralExhaustion.Graph.FanClosedPort
import StructuralExhaustion.Graph.FanClosedPortMass
import StructuralExhaustion.Graph.DegreeFourFanLedger
import StructuralExhaustion.Graph.FiniteCertificateMarking
import StructuralExhaustion.Graph.HybridFanIncidence
import StructuralExhaustion.Graph.PackedBridgeReduction

namespace EvenCycleExample.ConcreteK4

open StructuralExhaustion

/-! Closed executable fixture for the complete CT6→CT9→CT1 pipeline. -/

inductive Vertex where
  | v0 | v1 | v2 | v3
  deriving Repr, DecidableEq

/-- The machine schedule is explicit and independent of Mathlib's unordered
finite-set views. -/
@[implicit_reducible]
def vertices : FinEnum Vertex :=
  FinEnum.ofNodupList [.v0, .v1, .v2, .v3]
    (by intro vertex; cases vertex <;> simp) (by decide)

def graph : SimpleGraph Vertex := ⊤

def input : Graph.FiniteInput graph where
  vertices := vertices
  decideAdj := by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance

instance graphDecidableAdj : DecidableRel graph.Adj := input.decideAdj

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

theorem minimumDegreeThree : Baseline object := by
  change 3 ≤ object.minDegree
  native_decide

/-! ## Independent transfer of the surplus-activity CT6 profile -/

/-- A non-Erdős minimum-degree-cycle problem used only to demonstrate that
the shared surplus profile is not tied to the power-of-two predicate. -/
def surplusBase : Graph.MinimumDegreeCycle.StaticInput Vertex (fun _ => Unit) where
  minimumDegree := 3
  LengthOK := fun length => length % 2 = 0

theorem k4DeletionCritical (dart : object.graph.Dart) :
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := by
  left
  cases dart.fst <;> native_decide

def surplusCT6Run :=
  Graph.SurplusPortActivity.run surplusBase object
    (by
      change 3 ≤ object.minDegree
      exact minimumDegreeThree) k4DeletionCritical

theorem surplusCT6_terminal :
    surplusCT6Run.execution.terminal = .activeLedger :=
  surplusCT6Run.terminal_eq

theorem surplusCT6_total_zero : surplusCT6Run.residual.total = 0 := by
  native_decide

def surplusPairInput :=
  Graph.SurplusPortActivity.pairInput surplusBase object
    (by
      change 3 ≤ object.minDegree
      exact minimumDegreeThree) k4DeletionCritical

def surplusPairBoundedRun :=
  Graph.SurplusPortActivity.pairBoundedRunOfCardinalityLeOne surplusBase object
    (by
      change 3 ≤ object.minDegree
      exact minimumDegreeThree) k4DeletionCritical (by native_decide)

theorem surplusPair_bounded_terminal :
    surplusPairBoundedRun.execution.terminal = .bounded :=
  surplusPairBoundedRun.terminal_eq

theorem surplusPair_bounded_trace :
    surplusPairBoundedRun.execution.trace =
      [.entry, .partition, .overload, .boundedTerminal] :=
  surplusPairBoundedRun.trace_eq

/-! ## Materialized tactic executions -/

def path := (chosenMaximalPath object minimumDegreeThree).2.path

def ct6Execution := (ct6Run object minimumDegreeThree).execution

def ct9Execution := (ct9Run object minimumDegreeThree).execution

def evenCycle := evenCycleCertificate object minimumDegreeThree

def ct1Run := finalCT1Run object minimumDegreeThree

/-! ## Closed computational observations -/

theorem chosen_path_vertices :
    path.vertices = [.v3, .v2, .v1, .v0] := by
  native_decide

theorem endpoint_neighbor_items_exact :
    (endpointNeighborItems object minimumDegreeThree).values =
      [.v0, .v1, .v2] := by
  native_decide

theorem extracted_even_cycle_support :
    evenCycle.walk.support = [.v3, .v2, .v1, .v0, .v3] := by
  native_decide

theorem extracted_even_cycle_length : evenCycle.walk.length = 4 := by
  native_decide

/-! ## Exact terminals and traces -/

theorem ct6_terminal_activeLedger :
    ct6Execution.terminal = .activeLedger :=
  (ct6Run object minimumDegreeThree).terminal_eq

theorem ct6_trace_exact :
    ct6Execution.trace =
      [.entry, .firstFailureSearch, .activeLedgerTerminal] :=
  (ct6Run object minimumDegreeThree).trace_eq

theorem ct9_terminal_overloaded :
    ct9Execution.terminal = .overloaded :=
  (ct9Run object minimumDegreeThree).terminal_eq

theorem ct9_trace_exact :
    ct9Execution.trace =
      [.entry, .partition, .overload, .overloadedTerminal] :=
  (ct9Run object minimumDegreeThree).trace_eq

theorem ct1_terminal_c1 :
    ct1Run.result.terminal = .c1 :=
  ct1Run.terminal_eq

theorem ct1_trace_exact :
    ct1Run.result.trace =
      [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  ct1Run.trace_eq

end EvenCycleExample.ConcreteK4

namespace EvenCycleExample.ConcreteK34

open StructuralExhaustion

/-! The textbook complete bipartite graph `K₃,₄` exercises the overload side
of the same graph-owned CT6-to-CT9 surplus-pair transition. -/

abbrev Vertex := Fin 3 ⊕ Fin 4

def graph : SimpleGraph Vertex :=
  completeBipartiteGraph (Fin 3) (Fin 4)

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    intro left right
    cases left <;> cases right
    · exact .isFalse (by simp [graph, completeBipartiteGraph])
    · exact .isTrue (by simp [graph, completeBipartiteGraph])
    · exact .isTrue (by simp [graph, completeBipartiteGraph])
    · exact .isFalse (by simp [graph, completeBipartiteGraph])

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def base : Graph.MinimumDegreeCycle.StaticInput Vertex (fun _ => Unit) where
  minimumDegree := 3
  LengthOK := fun length => length % 2 = 0

theorem baseline : base.problem.Baseline object := by
  change 3 ≤ object.minDegree
  native_decide

theorem leftDegree (vertex : Fin 3) :
    object.degree (Sum.inl vertex) = 4 := by
  fin_cases vertex <;> native_decide

theorem rightDegree (vertex : Fin 4) :
    object.degree (Sum.inr vertex) = 3 := by
  fin_cases vertex <;> native_decide

theorem deletionCritical (dart : object.graph.Dart) :
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := by
  rcases dart with ⟨⟨first, second⟩, adjacent⟩
  rcases first with left | right <;>
    rcases second with otherLeft | otherRight
  · change graph.Adj (Sum.inl left) (Sum.inl otherLeft) at adjacent
    simp [graph, completeBipartiteGraph] at adjacent
  · exact Or.inr (rightDegree otherRight)
  · exact Or.inl (rightDegree right)
  · change graph.Adj (Sum.inr right) (Sum.inr otherRight) at adjacent
    simp [graph, completeBipartiteGraph] at adjacent

def surplusRun :=
  Graph.SurplusPortActivity.run base object baseline deletionCritical

def pairInput :=
  Graph.SurplusPortActivity.pairInput base object baseline deletionCritical

theorem pairItemCount : pairInput.items.values.length = 3 := by
  native_decide

def pairRun : CT9.OverloadedRun
    (Graph.SurplusPortActivity.pairCapability base object) pairInput :=
  Graph.SurplusPortActivity.pairRunOfTwoLe base object baseline
    deletionCritical (by native_decide)

def pair :=
  Graph.SurplusPortActivity.pairOfTwoLe base object baseline
    deletionCritical (by native_decide)

theorem pair_terminal : pairRun.execution.terminal = .overloaded :=
  pairRun.terminal_eq

theorem pair_trace : pairRun.execution.trace =
    [.entry, .partition, .overload, .overloadedTerminal] :=
  pairRun.trace_eq

theorem pair_distinct : pair.first ≠ pair.second :=
  pair.distinct

theorem pair_work_linear : pairInput.items.values.length ≤
    pairInput.items.values.length + 1 :=
  Graph.SurplusPortActivity.pairChecks_linear base object baseline
    deletionCritical

/-! The same non-Erdős graph also executes the framework-owned CT10
open/triangular surplus-port classifier. -/

theorem portClassification_verified :
    (Graph.SurplusPortActivity.classificationRun
      base object baseline deletionCritical).outcome.Valid :=
  Graph.SurplusPortActivity.classificationRun_verified
    base object baseline deletionCritical

theorem portClassification_stateSpace :
    (∃ cls : Graph.SurplusPortActivity.PortType,
        CT10.row
          (Graph.SurplusPortActivity.classificationCapability
            base object deletionCritical)
          (Graph.SurplusPortActivity.classificationInput
            base object baseline deletionCritical) cls = []) ∨
      (∀ cls : Graph.SurplusPortActivity.PortType,
        ∃ slot : Graph.SurplusPortActivity.ExcessPortSlot object,
          slot ∈ CT10.row
            (Graph.SurplusPortActivity.classificationCapability
              base object deletionCritical)
            (Graph.SurplusPortActivity.classificationInput
              base object baseline deletionCritical) cls) :=
  Graph.SurplusPortActivity.classification_stateSpace
    base object baseline deletionCritical

theorem portClassification_work_quadratic :
    Graph.SurplusPortActivity.classificationChecks object ≤
      2 * object.input.vertices.card ^ 2 + 2 :=
  Graph.SurplusPortActivity.classificationChecks_quadratic object

def openPortPairDecision :=
  Graph.SurplusPortActivity.openPairDecision
    base object baseline deletionCritical

theorem openPortPair_verified :
    (Graph.SurplusPortActivity.openPairResult
      base object baseline deletionCritical).outcome.Valid :=
  CT9.run_verified _ _

theorem openPortPair_work_cubic :
    Graph.SurplusPortActivity.openPairChecks object deletionCritical ≤
      object.input.vertices.card ^ 3 + object.input.vertices.card :=
  Graph.SurplusPortActivity.openPairChecks_cubic object deletionCritical

theorem shoulderLedger_terminal :
    (Graph.PortShoulderLedger.run
      base object baseline deletionCritical).terminal = .charge :=
  Graph.PortShoulderLedger.run_terminal_charge
    base object baseline deletionCritical

theorem shoulderLedger_total :
    CT5.ledgerTotal
      (Graph.PortShoulderLedger.spec base object deletionCritical)
      (Graph.PortShoulderLedger.capability base object deletionCritical)
      (Graph.PortShoulderLedger.context base object baseline) =
        2 * (Graph.SurplusPortActivity.portSlots object).card :=
  Graph.PortShoulderLedger.ledgerTotal_eq_twice_slots
    base object baseline deletionCritical

theorem shoulderLedger_work_quadratic :
    Graph.PortShoulderLedger.checks object ≤
      2 * object.input.vertices.card ^ 2 + 2 :=
  Graph.PortShoulderLedger.checks_quadratic object

end EvenCycleExample.ConcreteK34

namespace EvenCycleExample.SubdividedFiveStar

open StructuralExhaustion

/-! A subdivided five-star is a standard tree fixture for the exact overload
side of the open-port compatibility profile.  Its centre has degree five;
each of the five intermediate vertices has degree three after two pendant
leaves are attached. -/

abbrev Vertex := Fin 16

def orientedEdge (left right : Vertex) : Prop :=
  (left.1 = 0 ∧ 1 ≤ right.1 ∧ right.1 ≤ 5) ∨
    (1 ≤ left.1 ∧ left.1 ≤ 5 ∧
      (right.1 = 2 * left.1 + 4 ∨ right.1 = 2 * left.1 + 5))

instance orientedEdgeDecidable : DecidableRel orientedEdge := by
  intro left right
  unfold orientedEdge
  infer_instance

def graph : SimpleGraph Vertex := SimpleGraph.fromRel orientedEdge

def input : Graph.FiniteInput graph where
  vertices := inferInstance
  decideAdj := by
    intro left right
    change Decidable
      (left ≠ right ∧ (orientedEdge left right ∨ orientedEdge right left))
    infer_instance

def object : Graph.FiniteObject Vertex := ⟨graph, input⟩

def base : Graph.MinimumDegreeCycle.StaticInput Vertex (fun _ => Unit) where
  minimumDegree := 1
  LengthOK := fun length => Even length

theorem baseline : base.problem.Baseline object := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  change 1 ≤ object.minDegree
  native_decide

theorem intermediateDegree (vertex : Vertex)
    (lower : 1 ≤ vertex.1) (upper : vertex.1 ≤ 5) :
    object.degree vertex = 3 := by
  revert lower upper
  fin_cases vertex <;> native_decide

theorem deletionCritical (dart : object.graph.Dart) :
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := by
  rcases dart with ⟨⟨first, second⟩, adjacent⟩
  change (SimpleGraph.fromRel orientedEdge).Adj first second at adjacent
  rw [SimpleGraph.fromRel_adj] at adjacent
  rcases adjacent.2 with forward | backward
  · rcases forward with ⟨center, lower, upper⟩ |
      ⟨lower, upper, leaves⟩
    · exact Or.inr (intermediateDegree second lower upper)
    · exact Or.inl (intermediateDegree first lower upper)
  · rcases backward with ⟨center, lower, upper⟩ |
      ⟨lower, upper, leaves⟩
    · exact Or.inl (intermediateDegree first lower upper)
    · exact Or.inr (intermediateDegree second lower upper)

theorem noSquare : Graph.HighCenterStructure.NoSquare graph := by
  unfold Graph.HighCenterStructure.NoSquare
  intro a b c d aNeB aNeC aNeD bNeC bNeD cNeD
    ab bc cd da
  have aValNeB : a.1 ≠ b.1 := fun equal => aNeB (Fin.ext equal)
  have aValNeC : a.1 ≠ c.1 := fun equal => aNeC (Fin.ext equal)
  have aValNeD : a.1 ≠ d.1 := fun equal => aNeD (Fin.ext equal)
  have bValNeC : b.1 ≠ c.1 := fun equal => bNeC (Fin.ext equal)
  have bValNeD : b.1 ≠ d.1 := fun equal => bNeD (Fin.ext equal)
  have cValNeD : c.1 ≠ d.1 := fun equal => cNeD (Fin.ext equal)
  change (SimpleGraph.fromRel orientedEdge).Adj a b at ab
  change (SimpleGraph.fromRel orientedEdge).Adj b c at bc
  change (SimpleGraph.fromRel orientedEdge).Adj c d at cd
  change (SimpleGraph.fromRel orientedEdge).Adj d a at da
  simp only [SimpleGraph.fromRel_adj] at ab bc cd da
  unfold orientedEdge at ab bc cd da
  omega

theorem fourFree :
    ¬Graph.HasCycleWithLength graph Graph.HighCenterStructure.FourLength :=
  Graph.HighCenterStructure.fourFree_of_noSquare noSquare

def source : Graph.OpenPortCompatibility.SourceResidual
    base object baseline deletionCritical :=
  CT9.ExecutionResult.overloadResidual_of_terminal_eq
    (Graph.SurplusPortActivity.openPairCapability base object deletionCritical)
    (Graph.SurplusPortActivity.openPairInput
      base object baseline deletionCritical)
    (Graph.SurplusPortActivity.openPairResult
      base object baseline deletionCritical)
    (by native_decide)

def routedStage : Graph.OpenPortResponse.RoutedStage
    base object baseline deletionCritical source :=
  Graph.OpenPortResponse.routedStage
    base object baseline deletionCritical source

theorem routed_trace_valid : CT7.Graph.ValidTrace
    (Graph.AdjacencyResponse.spec base)
    (Graph.AdjacencyResponse.capability base)
    (Graph.AdjacencyResponse.context base object baseline)
    (Graph.OpenPortResponse.routedInput
      base object baseline deletionCritical source)
    (Graph.OpenPortResponse.run
      base object baseline deletionCritical source).trace :=
  routedStage.traceValid

theorem selected_pair_fanCompatible :
    Graph.OpenPortCompatibility.FanCompatible object
      (Graph.OpenPortCompatibility.firstSlot
        base object baseline deletionCritical source)
      (Graph.OpenPortCompatibility.secondSlot
        base object baseline deletionCritical source) := by
  apply Graph.OpenPortCompatibility.fanCompatible_of_nonadjacent object fourFree
  · exact Graph.OpenPortCompatibility.sourceSlots_sameCenter
      base object baseline deletionCritical source
  · exact Graph.OpenPortCompatibility.sourceSlots_distinct
      base object baseline deletionCritical source
  · letI : DecidableRel object.graph.Adj := object.input.decideAdj
    change ¬(SimpleGraph.fromRel orientedEdge).Adj
      (Graph.SurplusPortActivity.portEndpoint object
        (Graph.OpenPortCompatibility.firstSlot
          base object baseline deletionCritical source))
      (Graph.SurplusPortActivity.portEndpoint object
        (Graph.OpenPortCompatibility.secondSlot
          base object baseline deletionCritical source))
    rw [SimpleGraph.fromRel_adj]
    native_decide

theorem response_work_linear : Graph.AdjacencyResponse.checks object ≤
    2 * object.input.vertices.card + 1 :=
  Graph.AdjacencyResponse.checks_linear object

theorem centerZero_high : 4 ≤ object.degree (0 : Vertex) := by
  native_decide

def centerZeroPortStage : Graph.HighCenterPort.VerifiedStage base object baseline
    (0 : Vertex) centerZero_high deletionCritical fourFree :=
  Graph.HighCenterPort.verifiedStage base object baseline (0 : Vertex)
    centerZero_high deletionCritical fourFree

def centerZero_portDichotomy := centerZeroPortStage.dichotomy

theorem centerZero_classification_linear :
    Graph.HighCenterPort.classificationChecks object (0 : Vertex) ≤
      2 * object.input.vertices.card + 2 :=
  centerZeroPortStage.polynomial

end EvenCycleExample.SubdividedFiveStar

namespace EvenCycleExample.TriangularCompletionTransfer

open StructuralExhaustion

universe u

/-! A problem-independent transfer surface used outside the Erdős package.
It shows that the CT5 profile needs only the four explicit graph hypotheses,
not any Erdős arithmetic or minimal-counterexample structure. -/

variable {V : Type u}
variable (base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit))
variable (object : Graph.FiniteObject V)
variable (baseline : base.problem.Baseline object)
variable (center : V) (centerHigh : 4 ≤ object.degree center)
variable (threeLeMinimum : 3 ≤ base.minimumDegree)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (fourFree : ¬Graph.HasCycleWithLength object.graph
  Graph.HighCenterStructure.FourLength)

def setup : Graph.TriangularShoulderCompletion.Setup
    base object baseline center where
  centerHigh := centerHigh
  threeLeMinimum := threeLeMinimum
  deletionCritical := deletionCritical
  fourFree := fourFree

def stage : Graph.TriangularShoulderCompletion.VerifiedStage
    (setup base object baseline center centerHigh threeLeMinimum
      deletionCritical fourFree) :=
  Graph.TriangularShoulderCompletion.verifiedStage
    (setup base object baseline center centerHigh threeLeMinimum
      deletionCritical fourFree)

theorem completion_bookkeeping :
    Graph.TriangularShoulderCompletion.Bookkeeping
      (setup base object baseline center centerHigh threeLeMinimum
        deletionCritical fourFree) :=
  (stage base object baseline center centerHigh threeLeMinimum
    deletionCritical fourFree).bookkeeping

end EvenCycleExample.TriangularCompletionTransfer

namespace EvenCycleExample.BridgeReductionTransfer

open StructuralExhaustion

universe u

/-! Problem-independent transfer coverage for the framework-owned bridge
reduction.  No Erdős length arithmetic occurs in this namespace. -/

variable (input : Graph.PackedMinimumDegreeCycle.StaticInput)
variable (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
variable (ctx : Core.MinimalCounterexampleContext input.problem input.Target)

def stage : input.BridgeReductionStage minimumDegreeAtLeastTwo ctx :=
  input.bridgeReductionStage minimumDegreeAtLeastTwo ctx

include minimumDegreeAtLeastTwo in
theorem every_dart_nonbridging (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  (stage input minimumDegreeAtLeastTwo ctx).bridgeless dart

end EvenCycleExample.BridgeReductionTransfer

namespace EvenCycleExample.TriangularPortReturnTransfer

open StructuralExhaustion

universe u

/-! Problem-independent transfer coverage for the certificate-driven CT1
return profile.  The length predicate and graph hypotheses are arbitrary. -/

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (setup : Graph.TriangularPortReturn.Setup base object baseline center)
variable (port : Graph.TriangularPortReturn.TriPort setup)
variable (root : Graph.DartReturn object.graph
  (Graph.TriangularPortReturn.rootDart setup port))
variable (avoids : ¬Graph.HasCycleWithLength object.graph base.LengthOK)

noncomputable def stage : Graph.TriangularPortReturn.VerifiedStage
    setup port root avoids :=
  Graph.TriangularPortReturn.verifiedStage setup port root avoids

include avoids in
theorem constant_check_budget :
    (Graph.TriangularPortReturn.run setup port root).checks = 1 :=
  (stage setup port root avoids).checks

include avoids in
theorem exact_cycle_arithmetic :
    (Graph.TriangularPortReturn.certificate setup port root).cycle.length =
      (Graph.TriangularPortReturn.certificate setup port root).path.length + 2 :=
  (stage setup port root avoids).cycleLength

variable (noReturn :
  ¬Nonempty (Graph.TriangularPortReturn.Certificate setup port))

theorem avoiding_branch_zero_checks :
    (Graph.TriangularPortReturn.runAvoiding setup port noReturn).checks = 0 :=
  Graph.TriangularPortReturn.runAvoiding_checks setup port noReturn

end EvenCycleExample.TriangularPortReturnTransfer

namespace EvenCycleExample.TriangularFirstLandingTransfer

open StructuralExhaustion

universe u

/-! Transfer coverage for the exact CT10 first-landing profile and its
ordinary CT1-return composition.  The enclosing package remains the standard
even-cycle example; the reusable local theorem is independent of the target
length predicate. -/

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (setup : Graph.TriangularFirstLanding.Setup
  base object baseline center)

noncomputable def stage : Graph.TriangularFirstLanding.VerifiedStage setup :=
  Graph.TriangularFirstLanding.verifiedStage setup

theorem ct10_trace_valid :
    CT10.Graph.ValidTrace
      (Graph.TriangularFirstLanding.capability setup)
      (Graph.TriangularFirstLanding.input setup)
      (Graph.TriangularFirstLanding.run setup).trace :=
  (stage setup).traceValid

theorem ct10_total :
    ∃ result, result = Graph.TriangularFirstLanding.run setup ∧
      (result.terminal = .direct ∨ result.terminal = .promoted ∨
        result.terminal = .exhaustive) ∧
      CT10.Graph.ValidTrace
        (Graph.TriangularFirstLanding.capability setup)
        (Graph.TriangularFirstLanding.input setup) result.trace :=
  Graph.TriangularFirstLanding.run_total setup

theorem quadratic_work :
    Graph.TriangularFirstLanding.checks setup ≤
      6 * object.input.vertices.card ^ 2 + 3 :=
  (stage setup).polynomial

variable (port : Graph.TriangularPortReturn.TriPort setup)
variable (root : Graph.DartReturn object.graph
  (Graph.TriangularPortReturn.rootDart setup port))
variable (avoids : ¬Graph.HasCycleWithLength object.graph base.LengthOK)

include avoids in
theorem return_composition :
    Graph.TriangularFirstLanding.ClassifiedReturnAlternative
      (Graph.TriangularPortReturn.certificate setup port root) :=
  Graph.TriangularFirstLanding.classifyReturn
    (Graph.TriangularPortReturn.verifiedStage setup port root avoids)
    (stage setup)

end EvenCycleExample.TriangularFirstLandingTransfer

namespace EvenCycleExample.TriangularCrossShoulderTransfer

open StructuralExhaustion

universe u

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (setup : Graph.TriangularCrossShoulder.Setup
  base object baseline center)
variable (first second : Graph.TriangularCrossShoulder.TriPort setup)
variable (portsNe : first ≠ second)

def stage : Graph.TriangularCrossShoulder.VerifiedStage first second portsNe :=
  Graph.TriangularCrossShoulder.verifiedStage first second portsNe

include portsNe in
theorem exact_state_space :
    Graph.TriangularCrossShoulder.HighShoulder first second ∨
      CT9.fibreCount (Graph.TriangularCrossShoulder.capability first second)
        (Graph.TriangularCrossShoulder.input first second) () ≤ 1 :=
  (stage setup first second portsNe).stateSpace

include portsNe in
theorem constant_work :
    Graph.TriangularCrossShoulder.checks first second ≤ 5 :=
  (stage setup first second portsNe).polynomial

end EvenCycleExample.TriangularCrossShoulderTransfer

namespace EvenCycleExample.FanClosedPortTransfer

open StructuralExhaustion

universe u

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (profile : Graph.FanClosedPort.FanWindowProfile V)
variable (first second : Graph.FanClosedPort.OpenPort centerHigh deletionCritical)
variable (pair : Graph.FanClosedPort.CompatiblePair centerHigh deletionCritical
  first second)
variable (assigned : Graph.FanClosedPort.AssignedPair centerHigh
  deletionCritical profile first second)

def stage : Graph.FanClosedPort.VerifiedStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned :=
  Graph.FanClosedPort.verifiedStage centerHigh deletionCritical profile first
    second pair assigned

include assigned in
theorem two_closed_ports :
    Graph.FanClosedPort.FanClosed centerHigh deletionCritical profile first ∧
      Graph.FanClosedPort.FanClosed centerHigh deletionCritical profile second :=
  ⟨Graph.FanClosedPort.first_fanClosed centerHigh deletionCritical profile first
      second assigned,
    Graph.FanClosedPort.second_fanClosed centerHigh deletionCritical profile first
      second assigned⟩

include pair in
theorem four_distinct_carriers :
    (Graph.FanClosedPort.carriers centerHigh deletionCritical first second).Nodup :=
  Graph.FanClosedPort.carriers_nodup centerHigh deletionCritical first second pair

theorem constant_work : Graph.FanClosedPort.checks ≤ 10 :=
  by decide

end EvenCycleExample.FanClosedPortTransfer

namespace EvenCycleExample.FanClosedPortMassTransfer

open StructuralExhaustion

universe u

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (profile : Graph.FanClosedPort.FanWindowProfile V)
variable (first second : Graph.FanClosedPort.OpenPort centerHigh deletionCritical)
variable (pair : Graph.FanClosedPort.CompatiblePair centerHigh deletionCritical
  first second)
variable (assigned : Graph.FanClosedPort.AssignedPair centerHigh
  deletionCritical profile first second)

def stage : Graph.FanClosedPortMass.VerifiedStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned :=
  Graph.FanClosedPortMass.verifiedStage centerHigh deletionCritical profile
    first second pair assigned

include pair assigned in
theorem actual_count_at_least_two :
    2 ≤ (Graph.FanClosedPortMass.cubicClosedNeighbors
      (object := object) (center := center) profile).card :=
  Graph.FanClosedPortMass.two_le_cubicClosed_card centerHigh
    deletionCritical profile first second pair assigned

include pair assigned in
theorem positive_quarter_deficit_numerator :
    0 < Graph.FanClosedPortMass.deficitNumerator (object.degree center)
      (Graph.FanClosedPortMass.cubicClosedNeighbors
        (object := object) (center := center) profile).card :=
  Graph.FanClosedPortMass.deficitNumerator_positive centerHigh
    (Graph.FanClosedPortMass.two_le_cubicClosed_card centerHigh
      deletionCritical profile first second pair assigned)

include pair assigned in
theorem routed_terminal :
    (Graph.FanClosedPortMass.run (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned).terminal =
      .capacity :=
  (stage (base := base) (baseline := baseline) centerHigh deletionCritical
    profile first second pair assigned).terminal

end EvenCycleExample.FanClosedPortMassTransfer

namespace EvenCycleExample.DegreeFourFanLedgerTransfer

open StructuralExhaustion

universe u

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (Assigned : Graph.FanClosedPort.LocalCarrier V → Prop)
variable (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
variable (degreeFour : object.degree center = 4)

def stage : Graph.DegreeFourFanLedger.VerifiedStage object center centerHigh
    deletionCritical Assigned assignedDecidable
    (Graph.FanClosedPortMass.context base object baseline) degreeFour :=
  Graph.DegreeFourFanLedger.verifiedStage object center centerHigh
    deletionCritical Assigned assignedDecidable
    (Graph.FanClosedPortMass.context base object baseline) degreeFour

include base baseline centerHigh deletionCritical Assigned assignedDecidable
  degreeFour in
theorem exact_center_surplus : object.degree center - 3 = 1 :=
  (stage (base := base) (baseline := baseline) centerHigh deletionCritical
    Assigned assignedDecidable degreeFour).centerSurplus

include degreeFour in
theorem exact_local_sign_split :
    (Graph.DegreeFourFanLedger.closedCount object center centerHigh
        deletionCritical Assigned assignedDecidable
        (Graph.FanClosedPortMass.context base object baseline) ≤ 1 ∧
      Graph.DegreeFourFanLedger.quarterDeficit object center centerHigh
        deletionCritical Assigned assignedDecidable
        (Graph.FanClosedPortMass.context base object baseline) ≤ 0) ∨
    (2 ≤ Graph.DegreeFourFanLedger.closedCount object center centerHigh
        deletionCritical Assigned assignedDecidable
        (Graph.FanClosedPortMass.context base object baseline) ∧
      0 < Graph.DegreeFourFanLedger.quarterDeficit object center centerHigh
        deletionCritical Assigned assignedDecidable
        (Graph.FanClosedPortMass.context base object baseline)) :=
  (stage (base := base) (baseline := baseline) centerHigh deletionCritical
    Assigned assignedDecidable degreeFour).signSplit

include base baseline centerHigh deletionCritical Assigned assignedDecidable
  degreeFour in
theorem local_linear_budget :
    Graph.DegreeFourFanLedger.checks object center ≤
      17 * (object.input.vertices.card + 1) :=
  (stage (base := base) (baseline := baseline) centerHigh deletionCritical
    Assigned assignedDecidable degreeFour).polynomial

end EvenCycleExample.DegreeFourFanLedgerTransfer

namespace EvenCycleExample.FiniteCertificateMarkingTransfer

open StructuralExhaustion

/-! A two-site textbook transfer for the exact node `[80]` machinery.  The
certificate is already assigned at `false` and absent at `true`; no
certificate family is searched. -/

def context : Core.BranchContext
    ConcreteK4.surplusBase.problem :=
  Graph.FanClosedPortMass.context ConcreteK4.surplusBase ConcreteK4.object
    ConcreteK4.minimumDegreeThree

def profile : Graph.FiniteCertificateMarking.Profile Bool where
  sites := Core.Enumeration.bool
  Certificate := fun _site => Unit
  assigned := fun site => if site then none else some ()

def stage : profile.VerifiedStage context :=
  profile.verifiedStage context

theorem false_is_marked :
    Nonempty (profile.Marked context false) := by
  rcases profile.marked_or_residual context false with marked | residual
  · exact marked
  · have missing := residual.missing
    simp [profile] at missing

noncomputable def falseMarked : profile.Marked context false :=
  Classical.choice false_is_marked

theorem marked_terminal :
    (profile.run context false).terminal = .capacity :=
  falseMarked.terminal

theorem marked_trace :
    (profile.run context false).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] :=
  falseMarked.trace

theorem true_is_residual : profile.Residual context true := by
  rcases profile.marked_or_residual context true with marked | residual
  · rcases marked with ⟨marked⟩
    have present := marked.present
    simp [profile] at present
  · exact residual

theorem residual_terminal :
    (profile.run context true).terminal = .missingLabel :=
  true_is_residual.terminal

theorem residual_trace :
    (profile.run context true).trace =
      [.entry, .lowerMass, .memberScan, .missingLabelTerminal] :=
  true_is_residual.trace

theorem totality_and_linear_work :
    (∀ site : Bool,
      Nonempty (profile.Marked context site) ∨ profile.Residual context site) ∧
      profile.checks ≤ profile.budget.coefficient *
        (profile.budget.size () + 1) ^ profile.budget.degree :=
  ⟨stage.exhaustive, stage.polynomial⟩

end EvenCycleExample.FiniteCertificateMarkingTransfer

namespace EvenCycleExample.HybridFanIncidenceTransfer

open StructuralExhaustion

universe u

variable {V : Type u}
variable {base : Graph.MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : Graph.FiniteObject V}
variable {baseline : base.problem.Baseline object}
variable {center : V}
variable (centerHigh : 4 ≤ object.degree center)
variable (degreeLeEight : object.degree center ≤ 8)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (fourFree : ¬Graph.HasCycleWithLength object.graph
  Graph.HighCenterStructure.FourLength)
variable (profile : Graph.FanClosedPort.FanWindowProfile V)
variable (first second : Graph.FanClosedPort.OpenPort centerHigh deletionCritical)
variable (pair : Graph.FanClosedPort.CompatiblePair centerHigh deletionCritical
  first second)
variable (assigned : Graph.FanClosedPort.AssignedPair centerHigh
  deletionCritical profile first second)

def stage : Graph.HybridFanIncidence.VerifiedStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned fourFree degreeLeEight :=
  Graph.HybridFanIncidence.verifiedStage centerHigh deletionCritical profile
    first second pair assigned fourFree degreeLeEight

include fourFree in
theorem actual_endpoints_are_disjoint :
    Function.Injective (fun incidence : Graph.HybridFanIncidence.Incidence
      (object := object) (center := center) profile =>
        Graph.HybridFanIncidence.other (object := object) (center := center)
          profile incidence.1 incidence.2) :=
  Graph.HybridFanIncidence.other_injective profile fourFree

include degreeLeEight in
theorem half_credit_pays_with_slack :
    (3 : Int) ≤
      (Graph.HybridFanIncidence.totalQuarterCredit
          (object := object) (center := center) profile : Int) -
        Graph.FanClosedPortMass.deficitNumerator (object.degree center)
          (Graph.HybridFanIncidence.closedMembers
            (object := object) (center := center) profile).card :=
  Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack
    profile degreeLeEight

include pair assigned fourFree degreeLeEight in
theorem routed_terminal :
    (Graph.HybridFanIncidence.run (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned).terminal =
      .capacity :=
  (stage (base := base) (baseline := baseline) centerHigh degreeLeEight
    deletionCritical fourFree profile first second pair assigned).terminal

end EvenCycleExample.HybridFanIncidenceTransfer
