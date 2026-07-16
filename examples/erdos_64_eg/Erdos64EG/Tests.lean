import Erdos64EG.CT14PositiveDeficitCandidate
import Erdos64EG.CT14CertificateClosedCandidate
import Erdos64EG.CT12TypeBDemandSystem
import Erdos64EG.CT12TypeBCompletion
import Erdos64EG.CT12TypeBOverlapSupport
import Erdos64EG.CT12TypeBResolution
import Erdos64EG.CT14DegreeFourTypeBLedger
import Erdos64EG.CT14TypeBChoiceLedger
import Erdos64EG.CT14TypeBPostLedger
import Erdos64EG.CT12SparseEnvelope
import Erdos64EG.CT6SurplusPortActivation
import Erdos64EG.CT15BaselineSpineDemand
import Erdos64EG.CT15SparsePairResponses
import Erdos64EG.CT9AllPairAnchorLedger
import Erdos64EG.CT9CapacityTokenLedger
import Erdos64EG.CT9CoupledClassOverload
import Erdos64EG.CT9HomogeneousPattern
import Erdos64EG.CT10GeometricBottleneckClassification
import Erdos64EG.CT10SemanticBottleneckClassification
import Erdos64EG.SemanticBottleneckLocalConsumer
import Erdos64EG.SemanticBottleneckSwitchNormalization
import Erdos64EG.SemanticBottleneckLocalProjection
import Erdos64EG.SemanticBottleneckStrongFrontier
import Erdos64EG.SemanticBottleneckFirstClause
import Erdos64EG.SemanticBottleneckPairwiseClause
import Erdos64EG.P13RemainderResidual
import Erdos64EG.SurplusScaleSplit
import Erdos64EG.SparsePressureEnvelopeRoute
import Erdos64EG.CT14P13PositiveDeficiency
import Erdos64EG.CT15RemainderCurvature
import Erdos64EG.P13DensityConnectedRankPrefix
import Erdos64EG.P13LargeBudgetNetDeficiency
import Erdos64EG.P13ClosureRobustPartIV
import Erdos64EG.CT12DegreeFourB2Routing
import Erdos64EG.CT14TypeBResidualCenterLedger
import Erdos64EG.CT14TypeBLocalFanMass
import Erdos64EG.P13SameWindowStructuralFrontier
import Erdos64EG.P13Node21PartXIRoute
import Erdos64EG.P13SameWindowDyadicTerminal
import Erdos64EG.P13SameWindowBaseScaleSplit
import Erdos64EG.P13SameWindowShortThirdIncidence
import Erdos64EG.P13SameWindowNonRootChordResolution
import Erdos64EG.P13SameWindowOutsideBoundaryStar
import Erdos64EG.P13SameWindowNormalizedReturnBoundary
import Erdos64EG.P13SameWindowNormalizedReturnPackedSupportTransition
import Erdos64EG.P13SameWindowComponentBoundarySchedule
import Erdos64EG.P13SameWindowComponentD1D3Observation
import Erdos64EG.P13SameWindowComponentD1D3Ledger
import Erdos64EG.P13SameWindowComponentD4D7OrCoarseRepeat
import Erdos64EG.P13SameWindowComponentD4D7SemanticReadiness
import Erdos64EG.P13SameWindowComponentD4D7ClauseSchedule
import Erdos64EG.P13SameWindowComponentD4D7ClauseCursor
import Erdos64EG.P13SameWindowComponentD4LocalClauseRequest
import Erdos64EG.P13SameWindowComponentD4EvaluatorResidual
import Erdos64EG.P13SameWindowComponentD4EvaluatorConstructionResidual
import Erdos64EG.P13SameWindowPackedOwnerChange
import Erdos64EG.P13SameWindowCrossWindowTokenPair
import Erdos64EG.P13SameWindowLongSupportPrefix
import Erdos64EG.P13SameWindowLongPrefixStateLabels
import Erdos64EG.P13SameWindowLongPrefixDegreeRefinement
import Erdos64EG.P13SameWindowLongPrefixLocalClauseAlignment
import Erdos64EG.P13SameWindowLongPrefixExtendedClauseAlignment
import Erdos64EG.P13SameWindowLongPrefixThirdBlockClauseAlignment
import Erdos64EG.P13SameWindowLongPrefixFourthBlockClauseAlignment
import Erdos64EG.P13SameWindowLongPrefixCompatibleResponseFrontier

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

theorem k4_notCounterexample : ¬IsCounterexample k4 := by
  intro counterexample
  exact counterexample.2 k4Target

example :
    ∃ (exponent : Nat) (vertex : Fin 4)
      (cycle : k4.graph.Walk vertex vertex),
      exponent ≥ 2 ∧ cycle.IsCycle ∧ cycle.length = 2 ^ exponent :=
  officialConclusion_of_notCounterexample k4 k4_notCounterexample k4_baseline

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

noncomputable def exactPackingCeiling : P13CoverageResidual ctx packingPrefix where
  windowCeiling := p13 ctx
  packing_le := Nat.le_refl _

example : (exactPackingCeiling ctx packingPrefix).remainderFloor ≤
    (p13RemainderVertices ctx).card :=
  p13Remainder_large ctx packingPrefix
    (exactPackingCeiling ctx packingPrefix)

example : VerifiedP13RemainderContinuation ctx packingPrefix
    (exactPackingCeiling ctx packingPrefix) :=
  p13Remainder_node26_exact ctx packingPrefix
    (exactPackingCeiling ctx packingPrefix)
    (verifiedP13RemainderResidual ctx packingPrefix
      (exactPackingCeiling ctx packingPrefix))

/-! The strict Part-IV predecessor cannot bypass node `[24]`: even this
identity ceiling must be packaged against the packing literally retained by
node `[21]`. -/

variable (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)

noncomputable def exactNode21Coverage : P13CoverageResidual ctx
    (p13MultiScalePackingPrefix node21) where
  windowCeiling := p13 ctx
  packing_le := Nat.le_refl _

example (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx ≤
      p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card :=
  node24.packingDensityCap

noncomputable example : P13DensityConnectedGlobalRankPrefix ctx node21
    (exactNode21Coverage ctx node21) :=
  p13DensityConnectedGlobalRankPrefix ctx node21
    (exactNode21Coverage ctx node21)

example (joined : P13DensityConnectedGlobalRankPrefix ctx node21
    (exactNode21Coverage ctx node21)) :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  densityConnected_fullRankCount joined

example (joined : P13DensityConnectedGlobalRankPrefix ctx node21
    (exactNode21Coverage ctx node21))
    (budget : P13QuarterNetBudget ctx (node21 := node21)
      (exactNode21Coverage ctx node21)) :
    4 * ((p13RemainderCurvatureProfile ctx).positiveDeficiency -
        StructuralExhaustion.Graph.InducedPathWindowLedger.remainderSurplus
          ctx.G.object) <
      (p13RemainderVertices ctx).card :=
  p13NetDeficiency_strict_quarter_explicit joined budget

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

noncomputable example (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) (center : scope.Center) :
    Nonempty (scope.CertificateMarkedDegreeFourCenter noHigher center) ∨
      scope.FanCertificateResidualCenter noHigher center :=
  scope.certificateMarked_or_fanCertificateResidual noHigher center

example (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) (center : scope.Center)
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.assignedMarkedFan center.1 = none :=
  residual.assignedMarkedFan_eq_none

noncomputable example (scope : TypeBSupportScope ctx) :
    scope.degreeFourCertificateChecks ≤
      23 * (ctx.G.object.input.vertices.card + 1) ^ 2 :=
  scope.degreeFourCertificateChecks_polynomial

example : ctx.G.object.edgeCount ≤
    2 * ctx.G.object.input.vertices.card - 2 :=
  sparseEnvelope_edgeBound ctx

example : sparseSurplus ctx =
    (ctx.G.object.input.vertices.card : Int) - 6 -
      2 * sparseSlack ctx :=
  sparseSlack_surplus_identity ctx

example : (runSparseEnvelopeCT12 ctx).terminal = .exhausted :=
  runSparseEnvelopeCT12_terminal ctx

example : (runSparseEnvelopeCT12 ctx).iterations =
    (sparseEnvelopeRemaining ctx).input.vertices.card :=
  runSparseEnvelopeCT12_iterations ctx

example :
    (Graph.SurplusPortActivation.activatedSchedule
      (surplusPortActivationSetup ctx)
      (activatedSurplusStage ctx).run.residual).length =
        (ctx.G.object.input.vertices.orderedValues.map
          (fun center ↦ ctx.G.object.degree center - 3)).sum :=
  activatedSurplusSchedule_length_eq_sigma ctx

example (slot : ActiveSurplusSlot ctx) :
    Nonempty (ActiveSurplusDemand ctx slot) :=
  ⟨activeSurplusDemand ctx slot⟩

example :
    ((sparseEnvelopeProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((sparseEnvelopeProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((sparseEnvelopeProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree :=
  runSparseEnvelopeCT12_linearBudget ctx

example : (baselineSpineProfile ctx).coordinates.card = 0 :=
  baselineSpineProfile_coordinateCount ctx

example :
    (baselineSpineProfile ctx).deficit (sparseEnvelopeContext ctx) =
      baselineSpineBitBudget ctx :=
  baselineSpineProfile_exactDeficit ctx

example : (runBaselineSpineCT15 ctx).terminal = .fullRankLedger :=
  runBaselineSpineCT15_terminal ctx

example : (runBaselineSpineCT15 ctx).trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] :=
  runBaselineSpineCT15_trace ctx

example : (runBaselineSpineCT15 ctx).outcome.Valid :=
  runBaselineSpineCT15_verified ctx

example : SparsePairCT15Verified ctx :=
  sparsePairCT15_verified ctx

example :
    (Graph.SurplusPairResponse.blockedPairEnumeration
        (sparsePairActivationStage ctx)).card +
      (Graph.SurplusPairResponse.freePairEnumeration
        (sparsePairActivationStage ctx)).card =
      (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card :=
  sparsePair_exact_partition ctx

example :
    (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card ≤
      ctx.G.object.input.vertices.card ^ 4 :=
  sparsePair_schedule_quartic ctx

example :
    (allPairTokenRoutingInput ctx).items.values.length =
      ((allPairTokenRoutingCapability ctx).labels.orderedValues.map fun label ↦
        CT9.fibreCount (allPairTokenRoutingCapability ctx)
          (allPairTokenRoutingInput ctx) label).sum :=
  allPairTokenRouting_noOvercounting ctx

example (pair : Graph.SurplusPairResponse.FreePair
    (allPairTokenRoutingStage ctx)) :
    Graph.SurplusPairTokenRouting.pairRole
      (allPairTokenRoutingStage ctx) pair.1 = .freeAnchor :=
  allPairTokenRouting_freeRole ctx pair

example (pair : Graph.SurplusPairResponse.BlockedPair
    (allPairTokenRoutingStage ctx)) :
    Graph.SurplusPairTokenRouting.pairRole
      (allPairTokenRoutingStage ctx) pair.1 =
        .blocked (Graph.SurplusTokenRole.admittedKind
          (Graph.SurplusPairResponse.canonicalBlocker
            (allPairTokenRoutingStage ctx) pair).value) :=
  allPairTokenRouting_blockedRole ctx pair

example :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) =
      (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card *
        ((allPairSlotEnumeration ctx).card * 5) :=
  allPairTokenRouting_checks ctx

example :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) ≤
      5 * ctx.G.object.input.vertices.card ^ 6 :=
  allPairTokenRouting_checks_polynomial ctx

example :
    (allPairSlotEnumeration ctx).card ≤
      ctx.G.object.input.vertices.card :=
  allPairTokenRouting_tokenCount_le_vertexCount ctx

example :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) ≤
      5 * ctx.G.object.input.vertices.card ^ 3 :=
  allPairTokenRouting_checks_cubic ctx

example :
    (Graph.SurplusPairTokenRouting.run
      (allPairTokenRoutingStage ctx)).outcome.Valid :=
  allPairTokenRouting_verified ctx

example :
    CT9.Graph.ValidTrace (allPairTokenRoutingCapability ctx)
      (allPairTokenRoutingInput ctx)
      (Graph.SurplusPairTokenRouting.run
        (allPairTokenRoutingStage ctx)).trace :=
  allPairTokenRouting_traceValid ctx

example
    (pair : Graph.SurplusPairResponse.BlockedPair
      (sparsePairActivationStage ctx)) :
    (Graph.SurplusPairResponse.canonicalBlocker
        (sparsePairActivationStage ctx) pair).value ∈
      ((Graph.SurplusPairResponse.localBlockerProfile
        (sparsePairActivationStage ctx)).candidates pair.1).values ∧
    (Graph.SurplusPairResponse.localBlockerProfile
      (sparsePairActivationStage ctx)).Blocks pair.1
        (Graph.SurplusPairResponse.canonicalBlocker
          (sparsePairActivationStage ctx) pair).value :=
  ⟨(Graph.SurplusPairResponse.canonicalBlocker_sound
      (sparsePairActivationStage ctx) pair).1,
    (Graph.SurplusPairResponse.canonicalBlocker_sound
      (sparsePairActivationStage ctx) pair).2.1⟩

example :
    ((baselineSpineProfile ctx).budget
        (sparseEnvelopeContext ctx)).checks () ≤
      ((baselineSpineProfile ctx).budget
          (sparseEnvelopeContext ctx)).coefficient *
        (((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).size () + 1) ^
          ((baselineSpineProfile ctx).budget
            (sparseEnvelopeContext ctx)).degree :=
  runBaselineSpineCT15_linearBudget ctx

/-! Regression coverage for nodes `[133]`--`[139]` and `[141]`.  Each term
consumes the same green minimal-counterexample context and the exact complete
pair ledger inherited from node `[130]`. -/

noncomputable example (windowSize remainderSize primitiveSize : Nat) :
    (coupledClassProfile ctx windowSize remainderSize primitiveSize).Decision
      ctx.toBranchContext (coupledClassItems ctx) :=
  coupledClassDecision ctx windowSize remainderSize primitiveSize

noncomputable example (windowSize remainderSize primitiveSize : Nat)
    (overload :
      (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
        ctx.toBranchContext (coupledClassItems ctx)) :
    Graph.SurplusClasswiseOverload.RoutedOverload
      (coupledClassActivationStage ctx)
      windowSize remainderSize primitiveSize :=
  coupledOverloadClassRoute ctx windowSize remainderSize primitiveSize overload

example (windowSize remainderSize primitiveSize : Nat)
    (within :
      (coupledClassProfile ctx windowSize remainderSize primitiveSize).WithinCapacity
        (coupledClassItems ctx)) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      (450 * Graph.SurplusClasswiseOverload.maxCap
          windowSize remainderSize primitiveSize + 1) *
        ctx.G.object.input.vertices.card :=
  noCoupledOverload_quadraticSpine ctx
    windowSize remainderSize primitiveSize within

example (windowSize remainderSize primitiveSize : Nat) :
    Graph.SurplusClasswiseOverload.checks
      (setup := surplusPortActivationSetup ctx)
      windowSize remainderSize primitiveSize ≤
        225 * ctx.G.object.input.vertices.card ^ 3 :=
  coupledClassChecks_cubic ctx windowSize remainderSize primitiveSize

/-! Regression coverage for the ten-node green expansion.  Every statement
below consumes the identical minimal-counterexample context retained by its
green predecessor endpoint. -/

noncomputable example (windowSize remainderSize primitiveSize : Nat) :
    SurplusScaleDecision ctx windowSize remainderSize primitiveSize :=
  (surplusScaleStage ctx windowSize remainderSize primitiveSize).decision

example (windowSize remainderSize primitiveSize : Nat) :
    surplusScaleCoefficient windowSize remainderSize primitiveSize *
        ctx.G.object.input.vertices.card <
          (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ∨
      (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
        surplusScaleCoefficient windowSize remainderSize primitiveSize *
          ctx.G.object.input.vertices.card :=
  surplusScale_exhaustive ctx windowSize remainderSize primitiveSize

example :
    (p13RemainderDeficiencyProfile ctx).positiveDeficiency =
      Finset.sum (p13RemainderVertices ctx) (fun vertex : ctx.G.Vertex =>
        3 - (p13RemainderDeficiencyProfile ctx).internalDegree vertex) :=
  p13Remainder_positiveDeficiency_eq ctx

example :
    (p13RemainderCurvatureProfile ctx).positiveDeficiency -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object ≤
      15 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
          Graph.InducedPathWindowLedger.windowSurplus ctx.G.object -
        Graph.InducedPathWindowLedger.remainderSurplus ctx.G.object :=
  p13Remainder_surplusAdjustedDeficiency ctx

example :
    (p13CurvatureCoordinates ctx).card =
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  p13CurvatureCoordinates_card_eq_wedgeCount ctx

example : (runP13CurvatureCT15 ctx).terminal = .fullRankLedger :=
  runP13CurvatureCT15_terminal ctx

example (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) :
    scope.DegreeFourB2Route noHigher :=
  scope.degreeFourB2Route noHigher

example (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) (center : scope.Center)
    (residual : scope.FanCertificateResidualCenter noHigher center) :
    scope.UnresolvedCenter :=
  scope.certificateResidual_is_unresolved noHigher center residual

example (scope : TypeBSupportScope ctx)
    (residualCenters : Finset scope.Center) :
    residualCenters.card ≤ scope.highCenterChargeProfile.assignedSurplus :=
  scope.residualCenters_card_le_assignedSurplus residualCenters

noncomputable example (windowSize remainderSize primitiveSize : Nat)
    (overload :
      (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
        ctx.toBranchContext (coupledClassItems ctx)) :
    Nonempty (Graph.SurplusHomogeneousPattern.Audit
      (homogeneousActivationStage ctx)
      windowSize remainderSize primitiveSize
      (coupledOverloadClassRoute ctx windowSize remainderSize primitiveSize overload)) :=
  ⟨homogeneousPatternAudit ctx windowSize remainderSize primitiveSize overload⟩

noncomputable example
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    SemanticBottleneckClassification ctx overload homogeneous :=
  semanticBottleneckClassification ctx overload homogeneous

example
    (overload : (coupledClassProfile ctx 49 49 49).Overload
      ctx.toBranchContext (coupledClassItems ctx))
    (homogeneous : Graph.SurplusHomogeneousPattern.Audit
      (geometricActivationStage ctx) 49 49 49
      (coupledOverloadClassRoute ctx 49 49 49 overload)) :
    Semantic.Classifier.classificationWork (geometricActivationStage ctx)
        (canonicalGeometricPredecessor ctx overload homogeneous).collision
        (canonicalGeometricPredecessor ctx overload homogeneous).semanticTrigger ≤
      234 * ctx.G.object.input.vertices.card + 7 :=
  semanticBottleneckClassificationWork_le_vertices ctx overload homogeneous

/-! Focused regression coverage for the reviewed pointwise cold fork and its
same-window structural continuation.  The dyadic consumer is tested only from
the proof-carrying computed-constructor package; no independent target cycle
is accepted. -/

noncomputable example : List (P13Node21PartXIEntry ctx node21) :=
  p13Node21PartXIRoutes ctx node21

example : (p13Node21PartXIRoutes ctx node21).length = p13 ctx :=
  p13Node21PartXIRoutes_length ctx node21

example :
    (p13Node21PartXIRoutesWithTag ctx node21 .surplus).length +
      (p13Node21PartXIRoutesWithTag ctx node21 .dyadic).length +
      (p13Node21PartXIRoutesWithTag ctx node21 .corridorHigh).length +
      (p13Node21PartXIRoutesWithTag ctx node21 .quiet).length = p13 ctx :=
  p13Node21PartXIRoutes_partition ctx node21

variable (selectedWindow : P13ActualSelectedWindow ctx)
variable (actualColdFork :
  P13ActualAttachmentColdFork ctx node21 selectedWindow)

noncomputable example :
    P13SameWindowStructuralFrontier actualColdFork :=
  runP13SameWindowStructuralFrontier actualColdFork

example :
    (∃ position high,
      runP13SameWindowStructuralFrontier actualColdFork =
        .surplus position high) ∨
    (∃ stub same hit targetProof target targetExact,
      runP13SameWindowStructuralFrontier actualColdFork =
        .dyadicTargetHit stub same hit targetProof target targetExact) ∨
    (∃ stub same hit noTarget high handoff handoffExact,
      runP13SameWindowStructuralFrontier actualColdFork =
        .corridorHighDegree stub same hit noTarget high handoff handoffExact) ∨
    (∃ stub same noEvent germ,
      runP13SameWindowStructuralFrontier actualColdFork =
        .quiet stub same noEvent germ) :=
  runP13SameWindowStructuralFrontier_exhaustive actualColdFork

example (branch : P13ComputedDyadicBranch actualColdFork) :
    branch.g1Run.result.terminal = .c1 :=
  branch.g1_terminal

example (branch : P13ComputedDyadicBranch actualColdFork) :
    branch.g1Run.checks = 1 :=
  branch.g1_checks

example (branch : P13ComputedDyadicBranch actualColdFork) : False :=
  branch.impossible

variable (quiet : P13SameWindowQuietOutput actualColdFork)

noncomputable example
    (short : P13SameWindowComputedShort actualColdFork quiet) :
    P13SameWindowShortThirdIncidence short :=
  runP13SameWindowShortThirdIncidence short

example (short : P13SameWindowComputedShort actualColdFork quiet) :
    (∃ member, runP13SameWindowShortThirdIncidence short =
      .nonRootChord member) ∨
    (∃ outside, runP13SameWindowShortThirdIncidence short =
      .outsideBoundary outside) :=
  runP13SameWindowShortThirdIncidence_exhaustive short

example (short : P13SameWindowComputedShort actualColdFork quiet) :
    Graph.DeletedEdgeReturnThirdIncidence.visibleChecks short.setup ≤
      2 * ctx.G.object.input.vertices.card + 3 +
        p13ColdD1D3BaseThreshold :=
  p13SameWindowShortThirdIncidence_visibleChecks_le short

variable {short : P13SameWindowComputedShort actualColdFork quiet}

noncomputable example
    (chord : P13SameWindowComputedNonRootChord short) :
    P13SameWindowShorterReturn chord :=
  runP13SameWindowNonRootChordResolution chord

example (chord : P13SameWindowComputedNonRootChord short) :
    (runP13SameWindowNonRootChordResolution chord).shorter =
      chord.genericInput.shorterReturn :=
  runP13SameWindowNonRootChordResolution_shorterExact chord

example (chord : P13SameWindowComputedNonRootChord short) :
    (runP13SameWindowNonRootChordResolution chord).shorter.path.length <
      short.setup.returnPath.path.length :=
  runP13SameWindowNonRootChordResolution_strict chord

example (chord : P13SameWindowComputedNonRootChord short) :
    Graph.DeletedEdgeReturnChordResolution.visibleChecks chord.genericInput ≤
      p13ColdD1D3BaseThreshold + 1 :=
  p13SameWindowNonRootChordResolution_visibleChecks_le chord

noncomputable example
    (outside : P13SameWindowComputedOutsideBoundary short) :
    Graph.CubicStar.Data ctx.G.object quiet.stub.neighbor :=
  outside.cubicStar

noncomputable example
    (outside : P13SameWindowComputedOutsideBoundary short) :
    outside.cubicStar.SwitchBoundaryShape :=
  outside.switchBoundaryShape

example (outside : P13SameWindowComputedOutsideBoundary short)
    (vertex : ctx.G.Vertex)
    (adjacent : ctx.G.object.graph.Adj quiet.stub.neighbor vertex) :
    ∃ index, outside.switchBoundaryShape.boundaryVertex index = vertex :=
  outside.ownsAllRootIncidences vertex adjacent

example (outside : P13SameWindowComputedOutsideBoundary short) :
    outside.graphBranch.additionalChecks = 0 :=
  outside.additionalChecks_eq_zero

noncomputable example
    (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    P13SameWindowNormalizedReturnBoundary input :=
  runP13SameWindowNormalizedReturnBoundary input

example (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    (runP13SameWindowNormalizedReturnBoundary input).selectedReturn.path.support.length ≤
      p13ColdD1D3BaseThreshold :=
  runP13SameWindowNormalizedReturnBoundary_support_bounded input

example (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    (runP13SameWindowNormalizedReturnBoundary input).selectedReturn.path.length ≤
      short.setup.returnPath.path.length :=
  runP13SameWindowNormalizedReturnBoundary_length_le input

example (input : P13SameWindowNormalizedBoundaryInput (short := short)) :
    let result := runP13SameWindowNormalizedReturnBoundary input
    result.outsideVertex ∉ result.selectedReturn.path.support ∧
      ctx.G.object.graph.Adj quiet.stub.neighbor result.outsideVertex :=
  runP13SameWindowNormalizedReturnBoundary_outside input

example (computed : P13SameWindowComputedShorterBoundary short) :
    (runP13SameWindowNormalizedReturnBoundary
      (.rejectedChord computed)).selectedReturn.path.length <
        short.setup.returnPath.path.length :=
  runP13SameWindowNormalizedReturnBoundary_rejected_strict computed

example (computed : P13SameWindowComputedOutsideBoundary short) :
    (runP13SameWindowNormalizedReturnBoundary
      (.outsideBoundary computed)).selectedReturn.path.length =
        short.setup.returnPath.path.length :=
  runP13SameWindowNormalizedReturnBoundary_outside_length computed

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    P13SameWindowNormalizedReturnPackedSupportTransition computed :=
  runP13SameWindowNormalizedReturnPackedSupportTransition computed

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    (∃ supportSubset,
      runP13SameWindowNormalizedReturnPackedSupportTransition computed =
        .allInside supportSubset) ∨
    (∃ hit crossing stub stubExact endpoint endpointExact component componentExact,
      runP13SameWindowNormalizedReturnPackedSupportTransition computed =
        .firstTransition hit crossing stub stubExact endpoint endpointExact
          component componentExact) :=
  runP13SameWindowNormalizedReturnPackedSupportTransition_exhaustive computed

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks computed.graphInput =
      13 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object *
          ctx.G.object.input.vertices.card +
        13 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object +
        26 * Graph.InducedPathWindowLedger.packingNumber ctx.G.object *
          computed.graphInput.path.length :=
  p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_eq computed

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    (computed : P13SameWindowComputedNormalizedReturnBoundary input) :
    Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks computed.graphInput ≤
      ctx.G.object.input.vertices.card ^ 2 +
        (2 * p13ColdD1D3BaseThreshold + 1) *
          ctx.G.object.input.vertices.card :=
  p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_le computed

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :=
  transition.result

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.result.successor ≠ transition.stub ∧
      Graph.InducedPathColdSkeleton.component transition.result.successor =
        transition.component :=
  transition.successor_distinct_and_same_returned_component

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    ∃ hit, transition.graphInput.slotScan = .found hit ∧
      transition.graphInput.windowPosition.1 = hit.value ∧
      ∀ candidate ∈ hit.before,
        ¬transition.graphInput.SlotPredicate candidate :=
  transition.slot_first_hit_provenance

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    Graph.InducedPathComponentBoundarySchedule.visibleChecks
        transition.graphInput ≤
      50 * Graph.InducedPathComponentBoundarySchedule.localScale
        transition.graphInput ^ 3 :=
  transition.visibleChecks_polynomial

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    P13SameWindowComponentD1D3Residual transition :=
  runP13SameWindowComponentD1D3Observation transition

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    Nonempty
      (Graph.InducedPathColdSkeleton.TwoStubComponent.MissingD4D7Reconstruction
        transition.result
        (Graph.InducedPathComponentD1D3Observation.canonicalPath
          transition.graphInput)) :=
  p13SameWindowComponentD1D3_missing_d4_d7 transition

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    Graph.InducedPathComponentD1D3Observation.visibleChecks
        transition.graphInput ≤
      15 * (ctx.G.object.input.vertices.card + 1) :=
  p13SameWindowComponentD1D3_visibleChecks_linear transition

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    transition.D1D3LedgerOutput
      (computedP13SameWindowComponentD1D3LedgerSource transition) :=
  transition.runD1D3Ledger
    (computedP13SameWindowComponentD1D3LedgerSource transition)

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (transition : P13SameWindowFirstTransitionBoundaryInput computed) :
    Graph.InducedPathComponentD1D3Ledger.visibleChecks
        (transition.d1d3LedgerInput
          (computedP13SameWindowComponentD1D3LedgerSource transition)) ≤
      100 * Graph.InducedPathComponentD1D3Ledger.localScale
        (transition.d1d3LedgerInput
          (computedP13SameWindowComponentD1D3LedgerSource transition)) ^ 4 :=
  transition.d1d3Ledger_visibleChecks_polynomial
    (computedP13SameWindowComponentD1D3LedgerSource transition)

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (inside : P13SameWindowComputedAllInside computed) :
    P13SameWindowFirstCrossWindow inside :=
  runP13SameWindowPackedOwnerChange inside

example {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    (inside : P13SameWindowComputedAllInside computed) :
    Graph.InducedPathColdSkeletonOwnerChange.visibleChecks inside.graphInput ≤
      ctx.G.object.input.vertices.card ^ 2 +
        p13ColdD1D3BaseThreshold * (ctx.G.object.input.vertices.card + 1) :=
  p13SameWindowPackedOwnerChange_visibleChecks_le inside

noncomputable example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    {inside : P13SameWindowComputedAllInside computed}
    (cross : P13SameWindowFirstCrossWindow inside) :
    P13SameWindowCrossWindowTokenPair cross :=
  runP13SameWindowCrossWindowTokenPair cross

example
    {input : P13SameWindowNormalizedBoundaryInput (short := short)}
    {computed : P13SameWindowComputedNormalizedReturnBoundary input}
    {inside : P13SameWindowComputedAllInside computed}
    (cross : P13SameWindowFirstCrossWindow inside) :
    (runP13SameWindowCrossWindowTokenPair cross).leftToken =
        cross.crossing.leftToken ∧
      (runP13SameWindowCrossWindowTokenPair cross).rightToken =
        cross.crossing.rightToken :=
  runP13SameWindowCrossWindowTokenPair_source_exact cross

example : Routes.InducedPathCrossWindowTokenPair.additionalChecks = 0 :=
  p13SameWindowCrossWindowTokenPair_additionalChecks_eq_zero

noncomputable example
    (long : P13SameWindowLongOutput actualColdFork quiet) :
    P13SameWindowLongSupportPrefix actualColdFork quiet long :=
  runP13SameWindowLongSupportPrefix actualColdFork quiet long

example (long : P13SameWindowLongOutput actualColdFork quiet) :
    (Routes.LongFiniteSupportHandoff.prefixPositions
      (runP13SameWindowLongSupportPrefix
        actualColdFork quiet long).handoff.source).card =
      p13ColdD1D3BaseThreshold + 1 :=
  p13SameWindowLongSupportPrefix_card actualColdFork quiet long

example (long : P13SameWindowLongOutput actualColdFork quiet)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      (runP13SameWindowLongSupportPrefix
        actualColdFork quiet long).handoff.source) :
    (∃ index embeddingExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition
        (runP13SameWindowLongSupportPrefix
          actualColdFork quiet long).handoff.source position =
          .base index embeddingExact) ∨
    (∃ overflowExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition
        (runP13SameWindowLongSupportPrefix
          actualColdFork quiet long).handoff.source position =
          .overflow overflowExact) :=
  p13SameWindowLongSupportPrefixClass_exhaustive
    actualColdFork quiet long position

noncomputable example
    (long : P13SameWindowLongOutput actualColdFork quiet) :
    P13SameWindowLongPrefixStateLabels
      (p13SameWindowLongPrefixStateSource actualColdFork quiet long) :=
  runP13SameWindowLongPrefixStateLabels
    (p13SameWindowLongPrefixStateSource actualColdFork quiet long)

example (long : P13SameWindowLongOutput actualColdFork quiet) :
    let source := p13SameWindowLongPrefixStateSource actualColdFork quiet long
    (runP13SameWindowLongPrefixStateLabels source).routed.classification.terminal =
      CT10.Graph.Terminal.promoted :=
  runP13SameWindowLongPrefixStateLabels_ct10_terminal
    (p13SameWindowLongPrefixStateSource actualColdFork quiet long)

example (long : P13SameWindowLongOutput actualColdFork quiet) :
    Graph.LongPrefixObservedLabel.visibleChecks
        (p13SameWindowLongPrefixObservedInput
          (p13SameWindowLongPrefixStateSource actualColdFork quiet long)) +
      Routes.LongPrefixObservedLabel.semanticChecks
        (runP13SameWindowLongPrefixStateLabels
          (p13SameWindowLongPrefixStateSource actualColdFork quiet long)).routed.refinement ≤
      144 * (ctx.G.object.input.vertices.card + 1) + 9 :=
  runP13SameWindowLongPrefixStateLabels_totalVisibleChecks
    (p13SameWindowLongPrefixStateSource actualColdFork quiet long)

noncomputable example
    (scope : TypeBSupportScope ctx)
    (noHigher : scope.NoHigherCenter) :
    scope.LocalFanMassRoute noHigher :=
  scope.localFanMassRoute noHigher

example (scope : TypeBSupportScope ctx)
    (selected : Finset scope.Center) :
    selected.card ≤ scope.highCenterChargeProfile.assignedSurplus :=
  (scope.localFanMass selected).charged

end Erdos64EG.Tests
