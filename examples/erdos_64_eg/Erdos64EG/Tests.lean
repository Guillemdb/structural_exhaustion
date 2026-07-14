import Erdos64EG.CT14PositiveDeficitCandidate
import Erdos64EG.CT14CertificateClosedCandidate
import Erdos64EG.CT12TypeBDemandSystem
import Erdos64EG.CT12TypeBCompletion
import Erdos64EG.CT12TypeBOverlapSupport
import Erdos64EG.CT12TypeBResolution
import Erdos64EG.CT14TypeBChoiceLedger
import Erdos64EG.CT14TypeBPostLedger

namespace Erdos64EG.Tests

open StructuralExhaustion
open StructuralExhaustion.Graph
open Erdos64EG.Internal

/-!
Small executable smoke fixture for the first slice.  `K₄` satisfies the
official baseline and contains the explicitly certified four-cycle below, so
the generated CT1 machine is forced to its C1 terminal.
-/

def k4 : Object (Fin 4) where
  graph := ⊤
  input := {
    vertices := inferInstance
    decideAdj := inferInstance
  }

theorem k4_baseline : Baseline k4 := by
  change 3 ≤ (⊤ : SimpleGraph (Fin 4)).minDegree
  simp

def fourCycleWalk : k4.graph.Walk (0 : Fin 4) 0 :=
  letI : DecidableRel k4.graph.Adj := k4.input.decideAdj
  .cons (show k4.graph.Adj 0 1 by decide) <|
    .cons (show k4.graph.Adj 1 2 by decide) <|
      .cons (show k4.graph.Adj 2 3 by decide) <|
        .cons (show k4.graph.Adj 3 0 by decide) .nil

theorem fourCycleWalk_isCycle : fourCycleWalk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    decide
  · decide

theorem fourCycleWalk_powerOfTwo :
    PowerOfTwoLength fourCycleWalk.length := by
  change PowerOfTwoLength 4
  exact ⟨⟨2, by decide⟩, by decide, rfl⟩

def k4Cycle : CycleWithLength k4.graph PowerOfTwoLength :=
  {
    vertex := 0
    walk := fourCycleWalk
    isCycle := fourCycleWalk_isCycle
    length_ok := fourCycleWalk_powerOfTwo
  }

def k4Target : Target k4 := ⟨k4Cycle⟩

/-- The manuscript conversion deletes the first edge of the four-cycle and
produces the length-three Mersenne return in `K₄ - e`. -/
def k4MersenneReturn : MersenneReturn k4.graph :=
  EdgeRootedReturn.ofCycle k4Cycle

example : k4MersenneReturn.path.length = 3 := rfl

example : MersenneLength 3 := by
  exact (mersenneLength_iff 3).mpr ⟨2, by decide, rfl⟩

/-- End-to-end local validation of the explicit cycle certificate. -/
def k4CT1Run :
    StructuralExhaustion.CT1.CertifiedC1Run
      (ct1Spec (Fin 4)) (ct1Input k4 k4_baseline) :=
  runCT1 k4 k4_baseline k4Cycle

def k4MersenneCT1Run :
    StructuralExhaustion.CT1.CertifiedC1Run
      (ct1Spec (Fin 4)) (ct1Input k4 k4_baseline) :=
  runMersenneCT1 k4 k4_baseline k4MersenneReturn

example : k4MersenneCT1Run.result.terminal = .c1 :=
  k4MersenneCT1Run.terminal_eq

example : k4MersenneCT1Run.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  k4MersenneCT1Run.trace_eq

example : k4MersenneCT1Run.checks = 1 :=
  k4MersenneCT1Run.checks_eq

/-! Type-level regression coverage for manuscript node [8].  A retained
minimum-degree-three proper core executes the exact CT2 closure path, while
the exported theorem rules that branch out. -/

universe u

variable
  (ctx : StructuralExhaustion.Core.MinimalCounterexampleContext
    (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
      packedStaticInput)
    (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
      packedStaticInput))
  (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
  (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree)

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).terminal =
    .deletionC2 :=
  properCoreCT2Run_terminal ctx subgraph minimumDegreeThree

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).trace =
    [.entry, .deletionDecision, .deletionC2Terminal] :=
  properCoreCT2Run_trace ctx subgraph minimumDegreeThree

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).checks = 1 :=
  properCoreCT2Run_checks ctx subgraph minimumDegreeThree

example : subgraph.value.object.minDegree ≤ 2 :=
  properSubgraph_minDegree_le_two ctx subgraph

/-! Type-level regression coverage for the single CT3 stage spanning diagram
nodes [11]--[14].  The replacement is proof-specified, so the runner performs
one local certificate check and the exported theorem rules out the branch. -/

variable (verifiedPrefix : VerifiedBoundariedReplacementPrefix ctx)

example : VerifiedNoProperCorePrefix ctx :=
  boundariedReplacementPrefix_previous ctx verifiedPrefix

variable
  (TConcrete : Type u)
  (concreteBoundaries : FinEnum TConcrete)
  [Nonempty TConcrete]
  (concreteAtom : ConcreteCT3.ProperAtom ctx concreteBoundaries)
  (concreteCompression : ConcreteCT3.Compression concreteAtom)

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).terminal = .compression :=
  concreteCompression.run_terminal

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).trace =
      [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] :=
  concreteCompression.run_trace

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).checks = 1 :=
  concreteCompression.run_checks

example :
    (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
      concreteCompression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            concreteCompression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree :=
  concreteCompression.run_polynomial

example : ∃ result : CT3.CertifiedCompressionRun ctx
      concreteCompression.certifiedInput,
    result.terminal = .compression ∧
      result.trace = [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] :=
  concreteCompression.run_total

example : False := concreteCompression.impossible

example : False :=
  boundariedReplacementPrefix_uncompressible ctx verifiedPrefix
    concreteBoundaries concreteAtom concreteCompression

/-! Type-level regression coverage for the next single CT1 stage spanning
diagram nodes `[15]`--`[16]`.  The avoiding path is closed by the sole HSS
external theorem, and the forced induced-path certificate follows the exact
C1 path with one local validation check. -/

variable
  (p13Free : P13Free ctx)
  (p13Certificate : InducedP13Certificate ctx)

example : (runP13FreeCT1 ctx p13Free).result.terminal = .avoiding :=
  runP13FreeCT1_terminal ctx p13Free

example : (runP13FreeCT1 ctx p13Free).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal] :=
  runP13FreeCT1_trace ctx p13Free

example : (runP13FreeCT1 ctx p13Free).checks = 0 :=
  runP13FreeCT1_checks ctx p13Free

example : False :=
  p13FreeBranch_closed ctx p13Free

example : HasInducedP13 ctx :=
  inducedP13_of_hss ctx

example : (runInducedP13CT1 ctx p13Certificate).result.terminal = .c1 :=
  runInducedP13CT1_terminal ctx p13Certificate

example : (runInducedP13CT1 ctx p13Certificate).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .c1Terminal] :=
  runInducedP13CT1_trace ctx p13Certificate

example : (runInducedP13CT1 ctx p13Certificate).checks = 1 :=
  runInducedP13CT1_checks ctx p13Certificate

variable (p13Prefix : VerifiedInducedP13Prefix ctx)

example : VerifiedBoundariedReplacementPrefix ctx :=
  inducedP13Prefix_previous ctx p13Prefix

example : packedStaticInput.VerifiedInducedPathStage 13 ctx :=
  inducedP13Prefix_stage ctx p13Prefix

example : HasInducedP13 ctx :=
  inducedP13Prefix_realization ctx p13Prefix

/-! The next composed prefix consumes that exact CT1 output and retains the
maximum/maximal packing, CT12 audit, induced-`P₁₃`-free remainder, and no
internal three-core consequence. -/

variable (packingPrefix : VerifiedP13PackingPrefix ctx)

example : VerifiedInducedP13Prefix ctx :=
  p13PackingPrefix_previous ctx packingPrefix

example : Graph.InducedPathPacking.VerifiedStage ctx.G.object 13
    (by decide) ctx.toBranchContext :=
  p13PackingPrefix_stage ctx packingPrefix

example : p13Windows ctx ≠ [] :=
  p13PackingPrefix_nonempty ctx packingPrefix

example : (runP13PackingCT12 ctx).terminal = .exhausted :=
  runP13PackingCT12_terminal ctx

example : (runP13PackingCT12 ctx).iterations ≤
    ctx.G.object.input.vertices.card :=
  runP13PackingCT12_iterations ctx

example : (runP13PackingCT12 ctx).iterations = p13 ctx :=
  runP13PackingCT12_iterations_exact ctx

example : (p13RemainderVertices ctx).card + 13 * p13 ctx =
    ctx.G.object.input.vertices.card :=
  p13Remainder_partition ctx

example : Graph.InducedPathFree (p13Remainder ctx).graph 13 :=
  p13Remainder_free ctx

example : (p13Remainder ctx).InternalMinDegreeFree 3 :=
  packingPrefix.noInternalThreeCore

example : ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3 :=
  packingPrefix.noInternalSubgraphThreeCore

/-! Node `[18]` consumes that exact CT12 prefix.  CT10 exhausts the compact
`P₁₃` label universe, while the graph layer proves that every actual
attachment in the selected target-avoiding graph enters the accepted table. -/

variable (labelPrefix : VerifiedP13LabelAlgebraPrefix ctx)

example : VerifiedP13PackingPrefix ctx :=
  p13LabelAlgebraPrefix_previous ctx labelPrefix

example : p13LabelClassification.VerifiedStage ctx.toBranchContext :=
  p13LabelAlgebraPrefix_stage ctx labelPrefix

example : p13LabelClassification.candidateCount = 8192 :=
  p13Label_candidate_count

example : p13LabelClassification.classCount = 399 :=
  p13LegalLabel_count

example : p13LabelClassification.checks = 167792 :=
  p13Label_check_count

example : p13LabelClassification.checks ≤
    (p13LabelClassification.candidateCount + 1) ^ 2 :=
  p13Label_checks_quadratic

example : (runP13LabelCT10 ctx).terminal = .exhaustive :=
  runP13LabelCT10_terminal ctx

example : (runP13LabelCT10 ctx).trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  runP13LabelCT10_trace ctx

example : ∃ result : CT10.ExecutionResult
    (p13LabelClassification.capability PackedProblem.{u})
    (p13LabelCT10Input ctx),
    result.terminal = .exhaustive ∧
      result.trace =
        [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
      result.outcome.Valid ∧
      CT10.Graph.ValidTrace
        (p13LabelClassification.capability PackedProblem.{u})
        (p13LabelCT10Input ctx) result.trace :=
  runP13LabelCT10_total ctx

variable
  (path : SimpleGraph.pathGraph 13 ↪g ctx.G.object.graph)
  (outside : ctx.G.Vertex)
  (outsidePath : ∀ position : Fin 13, outside ≠ path position)
  (attached : ∃ position, ctx.G.object.graph.Adj outside (path position))

example : P13Legal
    (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside) :=
  p13AttachmentLabel_legal ctx labelPrefix path outside outsidePath attached

example : p13LabelClassification.Accepts
    (p13LabelEquiv.symm
      (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside)) :=
  p13AttachmentLabel_accepted ctx labelPrefix path outside outsidePath attached

/-! The next exact stage consumes CT6's actual active-ledger residual through
the registered CT6-to-CT9 route and partitions only the surplus-slot list. -/

variable (surplusPrefix : VerifiedSparseSurplusPrefix ctx)

example : (surplusPairInput ctx).context = sparseSurplusContext ctx :=
  surplusPairRoute_context_preserved ctx

example : (runSurplusPairCT9 ctx).outcome.Valid :=
  runSurplusPairCT9_verified ctx

example : CT9.Graph.ValidTrace (surplusPairCapability ctx)
    (surplusPairInput ctx) (runSurplusPairCT9 ctx).trace :=
  runSurplusPairCT9_traceValid ctx

example : ∃ result : CT9.ExecutionResult (surplusPairCapability ctx)
      (surplusPairInput ctx),
    result.outcome.Valid ∧ CT9.Graph.ValidTrace
      (surplusPairCapability ctx) (surplusPairInput ctx) result.trace :=
  runSurplusPairCT9_total ctx

variable (twoLeSigma : 2 ≤
  (ctx.G.object.input.vertices.orderedValues.map
    (fun center => ctx.G.object.degree center - 3)).sum)

example : (runSurplusPairCT9OfTwoLeSigma ctx twoLeSigma).execution.terminal =
    .overloaded :=
  (runSurplusPairCT9OfTwoLeSigma ctx twoLeSigma).terminal_eq

example : (surplusPairOfTwoLeSigma ctx twoLeSigma).first ≠
    (surplusPairOfTwoLeSigma ctx twoLeSigma).second :=
  surplusPairOfTwoLeSigma_distinct ctx twoLeSigma

/-! Subsequent finite stages remain on the same selected graph. -/

example : (runFourCycleAvoidingCT1 ctx).result.terminal = .avoiding :=
  runFourCycleAvoidingCT1_terminal ctx

example :
    (runSurplusPortClassificationCT10 ctx).outcome.Valid :=
  (surplusPortClassificationStage ctx).verified

example : (runOpenPortPairCT9 ctx).outcome.Valid :=
  (openPortPairStage ctx).verified

example :
    (∀ center, CT9.fibreCount (openPortPairCapability ctx)
      (openPortPairInput ctx) center ≤ 1) ∨
      (∃ source : Graph.OpenPortResponse.SourceResidual
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)),
        Graph.OpenPortResponse.RoutedStage
          (fixedPackedInput ctx) ctx.G.object
          (packedStaticInput.fixedContext ctx).baseline
          ((fixedPackedInput ctx).dart_has_tight_endpoint
            (packedStaticInput.fixedContext ctx)) source) :=
  openPortResponse_stateSpace ctx

example :
    (Graph.PortShoulderLedger.run
      (fixedPackedInput ctx) ctx.G.object
      (packedStaticInput.fixedContext ctx).baseline
      ((fixedPackedInput ctx).dart_has_tight_endpoint
        (packedStaticInput.fixedContext ctx))).terminal = .charge :=
  runPortShoulderLedgerCT5_terminal ctx

example : OpenPortCompatibilityState ctx :=
  openPortCompatibility_stateSpace ctx

example (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :
    HighCenterPortStage ctx center centerHigh :=
  highCenterPort_stage ctx center centerHigh

example (center : ctx.G.Vertex)
    (centerHigh : 4 ≤ ctx.G.object.degree center) :
    TriangularShoulderStage ctx center centerHigh :=
  triangularShoulder_stage ctx center centerHigh

example (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge :=
  dart_not_bridge ctx dart

example (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    (packedStaticInput.bridgeCT2Run (by decide) ctx dart bridge).terminal =
      .deletionC2 :=
  (bridgeReductionStage ctx).terminal dart bridge

example (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    (packedStaticInput.bridgeCT2Run (by decide) ctx dart bridge).checks = 1 :=
  (bridgeReductionStage ctx).checks dart bridge

variable (center : ctx.G.Vertex)
  (centerHigh : 4 ≤ ctx.G.object.degree center)
  (triangularPort : Graph.TriangularPortReturn.TriPort
    (triangularShoulderSetup ctx center centerHigh))

example : (Graph.TriangularPortReturn.certificate
    (triangularShoulderSetup ctx center centerHigh) triangularPort
    (triangularPortRoot ctx center centerHigh triangularPort)).path.IsPath :=
  (triangularPortReturnStage ctx center centerHigh triangularPort).pathIsSimple

example : (Graph.TriangularPortReturn.run
    (triangularShoulderSetup ctx center centerHigh) triangularPort
    (triangularPortRoot ctx center centerHigh triangularPort)).result.terminal = .c1 :=
  (triangularPortReturnStage ctx center centerHigh triangularPort).terminal

example : (Graph.TriangularPortReturn.run
    (triangularShoulderSetup ctx center centerHigh) triangularPort
    (triangularPortRoot ctx center centerHigh triangularPort)).checks = 1 :=
  (triangularPortReturnStage ctx center centerHigh triangularPort).checks

example (exponent : Nat) (lower : 2 ≤ exponent) :
    (Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) triangularPort
      (triangularPortRoot ctx center centerHigh triangularPort)).path.length ≠
        2 ^ exponent - 2 :=
  triangularPortReturn_length_ne ctx center centerHigh triangularPort exponent lower

example : CT10.Graph.ValidTrace
    (Graph.TriangularFirstLanding.capability
      (triangularShoulderSetup ctx center centerHigh))
    (Graph.TriangularFirstLanding.input
      (triangularShoulderSetup ctx center centerHigh))
    (Graph.TriangularFirstLanding.run
      (triangularShoulderSetup ctx center centerHigh)).trace :=
  (triangularFirstLandingStage ctx center centerHigh).traceValid

example : Graph.TriangularFirstLanding.ClassifiedReturnAlternative
    (Graph.TriangularPortReturn.certificate
      (triangularShoulderSetup ctx center centerHigh) triangularPort
      (triangularPortRoot ctx center centerHigh triangularPort)) :=
  triangularPortReturn_classified ctx center centerHigh triangularPort

variable (secondTriangularPort : Graph.TriangularCrossShoulder.TriPort
    (triangularShoulderSetup ctx center centerHigh))
  (triangularPortsNe : triangularPort ≠ secondTriangularPort)

example : Graph.TriangularCrossShoulder.HighShoulder triangularPort
      secondTriangularPort ∨
    CT9.fibreCount
      (Graph.TriangularCrossShoulder.capability triangularPort
        secondTriangularPort)
      (Graph.TriangularCrossShoulder.input triangularPort
        secondTriangularPort) () ≤ 1 :=
  triangularCrossShoulder_stateSpace ctx center centerHigh triangularPort
    secondTriangularPort triangularPortsNe

example : Graph.TriangularCrossShoulder.checks triangularPort
    secondTriangularPort ≤ 5 :=
  (triangularCrossShoulderStage ctx center centerHigh triangularPort
    secondTriangularPort triangularPortsNe).polynomial

noncomputable example
    (Assigned : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier)) :
    Graph.FanClosedPort.FanWindowProfile ctx.G.Vertex :=
  p13FanWindowProfile ctx Assigned assignedDecidable

example : Graph.FanClosedPort.checks = 10 :=
  Graph.FanClosedPort.checks_eq_ten

example {degree closedCount : Nat} (degreeHigh : 4 ≤ degree)
    (twoLe : 2 ≤ closedCount) :
    0 < Graph.FanClosedPortMass.deficitNumerator degree closedCount :=
  Graph.FanClosedPortMass.deficitNumerator_positive degreeHigh twoLe

example {degree closedCount : Nat} (degreeLeEight : degree ≤ 8) :
    (3 : Int) ≤ (4 * (closedCount : Int)) -
      Graph.FanClosedPortMass.deficitNumerator degree closedCount := by
  unfold Graph.FanClosedPortMass.deficitNumerator
  omega

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice) :
    Set.PairwiseDisjoint (↑support.fullDemandSet)
      (support.fullActualCoreSupport choice) :=
  support.fullActualCoreSupport_pairwiseDisjoint choice

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.assignedChargeProfile.centerQuarterCharge +
      ∑ vertex ∈ support.usedCore choice,
        support.assignedChargeProfile.coreQuarterChargeAt vertex :=
  support.processedFanCharge_nonnegative choice

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
      support.remainingQuarterCharge choice < 0 :=
  support.netQuarterCharge_nonnegative_or_remaining_negative choice

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice) :
    support.remainingInducedQuarterCharge choice =
      support.remainingQuarterCharge choice +
        support.remainingBoundaryCredit choice :=
  support.remainingInducedQuarterCharge_eq_raw_add_boundary choice

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice)
    (transfer : support.BoundaryTransfer choice) :
    0 ≤ support.assignedChargeProfile.netQuarterCharge :=
  support.netQuarterCharge_nonnegative_of_unsaturated_boundaryTransfer
    choice unsaturated transfer

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice)
    (overload : support.BoundaryOverload choice) :
    Nonempty (support.BoundaryLanding choice) :=
  support.boundaryOverload_has_landing choice overload

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice) :
    (support.processedCore choice).card ≤ 25 * support.centers.card :=
  support.processedCore_card_le_twentyFive_mul_centers choice

noncomputable example (support : TypeBAssignedSupport ctx)
    (choice : support.completionProfile.FullChoice)
    (unsaturated : support.RemainingUnsaturated choice) :
    -support.assignedChargeProfile.netQuarterCharge ≤
      800 * (support.assignedChargeProfile.assignedSurplus : Int) :=
  support.neg_netQuarterCharge_le_eightHundred_mul_assignedSurplus_of_unsaturated
    choice unsaturated

noncomputable example (scope : TypeBSupportScope ctx) :
    -scope.highCenterChargeProfile.netQuarterCharge ≤
      21 * (scope.highCenterChargeProfile.assignedSurplus : Int) +
        (scope.centerDeletedReceiverOverload : Int) :=
  scope.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_receiverOverload

noncomputable example (scope : TypeBSupportScope ctx) :
    scope.UnresolvedCenter ∨
      ∃ resolution : scope.FullResolution,
        let support := scope.assignedSupport resolution
        Nonempty support.MinimalOverlap ∨
          ∃ choice : support.completionProfile.FullChoice,
            0 ≤ support.assignedChargeProfile.netQuarterCharge ∨
              Nonempty (support.RemainingSaturated choice) ∨
                (support.assignedChargeProfile.netQuarterCharge < 0 ∧
                  support.BoundaryOverload choice ∧
                  Nonempty (support.BoundaryLanding choice) ∧
                  -support.assignedChargeProfile.netQuarterCharge ≤
                    800 *
                      (support.assignedChargeProfile.assignedSurplus : Int)) :=
  scope.unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload

end Erdos64EG.Tests
