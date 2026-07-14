import Erdos64EG
import Erdos64EG.Tests
import StructuralExhaustion.Canonical.ExampleExport

namespace Erdos64EG.WebExport

open StructuralExhaustion.Canonical

private def proofSliceWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "proof-slice"
  title := "Verified Erdős 64 prefix"
  purpose :=
    "Inspect the exact Mersenne target algebra, lexicographic minimal selection, CT2 criticality and bridge contraction, boundaried replacement, the HSS-forced induced-P13 CT1 stage, the routed maximum-packing CT12 remainder stage, the exhaustive CT10 P13 attachment-label algebra, the ordered CT6 degree-surplus ledger, the routed CT9 surplus-pair split, and the Type B development through its graph-derived high-center choice/overlap trichotomy."
  completion := .partialProof
  stages := [
    {
      stageId := "proof-slice.official"
      title := "Official Erdős 64 statement"
      summary := "The pinned public boundary asks for a power-of-two cycle in every finite graph of minimum degree at least three."
      kind := .problem
      primaryDeclaration := `Erdos64EG.OfficialStatement
    },
    {
      stageId := "proof-slice.internal"
      title := "Executable internal problem"
      summary := "The same Mathlib graph is paired with an explicit finite inspection order and an executable but equivalent length predicate."
      kind := .adapter
      primaryDeclaration := `Erdos64EG.Internal.staticInput
      evidenceDeclarations := [
        `Erdos64EG.Internal.powerOfTwoLength_iff,
        `Erdos64EG.Internal.target_iff_official_conclusion
      ]
    },
    {
      stageId := "proof-slice.k4-fixture"
      title := "K₄ Mersenne-return fixture"
      summary := "The explicit four-cycle is converted to a length-three return in the graph with its root edge deleted."
      kind := .fixture
      primaryDeclaration := `Erdos64EG.Tests.k4Cycle
      evidenceDeclarations := [
        `Erdos64EG.Tests.k4_baseline,
        `Erdos64EG.Tests.fourCycleWalk_isCycle,
        `Erdos64EG.Tests.fourCycleWalk_powerOfTwo,
        `Erdos64EG.Tests.k4MersenneReturn
      ]
    },
    {
      stageId := "proof-slice.ct1"
      title := "CT1 Mersenne target algebra"
      summary := "CT1 validates one rooted return or constructs the exact avoiding residual from disjoint return sets."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `Erdos64EG.Internal.runAvoidingCT1
      evidenceDeclarations := [
        `Erdos64EG.Internal.target_iff_hasMersenneReturn,
        `Erdos64EG.Internal.not_target_iff_returnSets_disjoint,
        `Erdos64EG.Internal.runMersenneCT1,
        `Erdos64EG.Tests.k4MersenneCT1Run
      ]
    },
    {
      stageId := "proof-slice.no-proper-core"
      title := "CT2 no proper core"
      summary := "A supplied proper finite subgraph is one certified local reduction; target transport and lexicographic minimality force its minimum degree to be at most two."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedNoProperCorePrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.properSubgraph_minDegree_le_two,
        `Erdos64EG.Internal.properCoreCT2Run_terminal,
        `Erdos64EG.Internal.properCoreCT2Run_trace,
        `Erdos64EG.Internal.properCoreCT2Run_checks,
        `Erdos64EG.Internal.noProperCorePrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_total,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_polynomial
      ]
    },
    {
      stageId := "proof-slice.ct2"
      title := "Routed CT2 deletion criticality"
      summary := "The certified CT1 residual enters local CT2 discovery; its exact disabled result forces every edge to have a degree-three endpoint."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedCT1CT2Prefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.localRoute_disabled,
        `Erdos64EG.Internal.deletionCriticality,
        `Erdos64EG.Internal.highDegree_independent,
        `Erdos64EG.Internal.verifiedCT1CT2Prefix
      ]
    },
    {
      stageId := "proof-slice.ct3"
      title := "CT3 boundaried replacement"
      summary := "Literal packed-graph CT3 gluing derives whole-rank decrease, minimum-degree preservation, and target transport from local replacement data."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedBoundariedReplacementPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.packedStaticInput,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.boundaryDegreeProfile_ne_not_targetComplete,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.targetComplete_contextUniversal,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_terminal,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_trace,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_total,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_checks,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_polynomial,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_lexRank_lt,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_preserves_minDegree,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible,
        `Erdos64EG.Internal.boundariedReplacementPrefix_previous,
        `Erdos64EG.Internal.boundariedReplacementPrefix_uncompressible
      ]
    },
    {
      stageId := "proof-slice.induced-p13"
      title := "CT1 induced-P₁₃ branch"
      summary := "One CT1 block covers diagram nodes [15]–[16]: literal P₁₃-freeness reaches the avoiding terminal, HSS closes it against dyadic-target avoidance, and the forced embedding reaches C1."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedInducedP13Prefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle,
        `Erdos64EG.Internal.runP13FreeCT1_terminal,
        `Erdos64EG.Internal.runP13FreeCT1_trace,
        `Erdos64EG.Internal.runP13FreeCT1_total,
        `Erdos64EG.Internal.runP13FreeCT1_polynomial,
        `Erdos64EG.Internal.hssTarget_of_p13Free,
        `Erdos64EG.Internal.p13FreeBranch_closed,
        `Erdos64EG.Internal.inducedP13_of_hss,
        `Erdos64EG.Internal.runInducedP13CT1_terminal,
        `Erdos64EG.Internal.runInducedP13CT1_trace,
        `Erdos64EG.Internal.runInducedP13CT1_total,
        `Erdos64EG.Internal.runInducedP13CT1_polynomial,
        `Erdos64EG.Internal.inducedP13Prefix_previous,
        `Erdos64EG.Internal.inducedP13Prefix_realization
      ]
    },
    {
      stageId := "proof-slice.p13-packing"
      title := "CT12 induced-P₁₃ packing"
      summary := "One CT12 stage selects a maximum vertex-disjoint induced-P₁₃ family, derives maximal saturation, audits exactly that selected list, and constructs the P₁₃-free remainder containing no finite subgraph of minimum degree three."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedP13PackingPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13PackingCT12_terminal,
        `Erdos64EG.Internal.runP13PackingCT12_iterations,
        `Erdos64EG.Internal.runP13PackingCT12_iterations_exact,
        `Erdos64EG.Internal.runP13PackingCT12_trace_bound,
        `Erdos64EG.Internal.p13_maximum,
        `Erdos64EG.Internal.p13_saturated,
        `Erdos64EG.Internal.p13Remainder_partition,
        `Erdos64EG.Internal.p13Remainder_free,
        `Erdos64EG.Internal.p13Remainder_componentwise_free,
        `Erdos64EG.Internal.p13Remainder_internalThreeCore_free,
        `Erdos64EG.Internal.p13Remainder_internalSubgraphThreeCore_free,
        `Erdos64EG.Internal.p13PackingPrefix_previous,
        `Erdos64EG.Internal.p13PackingPrefix_routeId,
        `Erdos64EG.Internal.p13PackingPrefix_routedInputExact,
        `Erdos64EG.Internal.p13PackingPrefix_nonempty
      ]
    },
    {
      stageId := "proof-slice.p13-labels"
      title := "CT10 P₁₃ attachment-label algebra"
      summary := "One CT10 stage classifies every nonempty attachment label on the fixed thirteen-position path, certifies the exact 399-row table and size distribution, and defines the manuscript compatibility and two-step curvature relations."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedP13LabelAlgebraPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13CodeLegal_iff_gapLegal,
        `Erdos64EG.Internal.p13Legal_iff_gapLegal,
        `Erdos64EG.Internal.p13LegalLabel_count,
        `Erdos64EG.Internal.p13LegalLabel_size_distribution,
        `Erdos64EG.Internal.legalP13Label_card_bounds,
        `Erdos64EG.Internal.p13Label_candidate_count,
        `Erdos64EG.Internal.p13Label_check_count,
        `Erdos64EG.Internal.p13Label_checks_quadratic,
        `Erdos64EG.Internal.runP13LabelCT10_terminal,
        `Erdos64EG.Internal.runP13LabelCT10_trace,
        `Erdos64EG.Internal.runP13LabelCT10_total,
        `Erdos64EG.Internal.p13C_eq_one_iff,
        `Erdos64EG.Internal.p13OmegaTwo_eq_one_iff,
        `Erdos64EG.Internal.p13AttachmentLabel_legal,
        `Erdos64EG.Internal.p13AttachmentLabel_accepted,
        `Erdos64EG.Internal.p13LabelAlgebraPrefix_previous,
        `Erdos64EG.Internal.p13LabelAlgebraPrefix_stage
      ]
    },
    {
      stageId := "proof-slice.surplus-ct6"
      title := "CT6 ordered surplus activity"
      summary := "CT6 scans the declared vertex order, retains the first high centre with a non-cubic neighbour if one exists, and otherwise produces the exact degree-surplus ledger; deletion criticality forces the active terminal."
      kind := .tactic
      tacticId? := some "CT6"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSparseSurplusPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.runSparseSurplusCT6_terminal,
        `Erdos64EG.Internal.runSparseSurplusCT6_trace,
        `Erdos64EG.Internal.runSparseSurplusCT6_total_eq_sigma,
        `Erdos64EG.Internal.sparseSurplus_excessPortSlot_card,
        `Erdos64EG.Internal.sparseSurplus_highCenter_neighbor_cubic,
        `Erdos64EG.Internal.runSparseSurplusCT6_checks_linear,
        `Erdos64EG.Internal.runSparseSurplusCT6_primitiveChecks_quadratic,
        `StructuralExhaustion.Graph.SurplusPortActivity.noFailure_of_deletionCritical
      ]
    },
    {
      stageId := "proof-slice.surplus-pairs"
      title := "CT9 surplus-pair availability"
      summary := "The registered CT6-to-CT9 route partitions exactly the degree-surplus slots: the bounded terminal certifies at most one slot, while overload returns two distinct slots. No blocker or return-path semantics are claimed."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSurplusPairPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.surplusPairRoute_id,
        `Erdos64EG.Internal.surplusPairRoute_context_preserved,
        `Erdos64EG.Internal.surplusPair_itemCount_eq_sigma,
        `Erdos64EG.Internal.runSurplusPairCT9_verified,
        `Erdos64EG.Internal.runSurplusPairCT9_traceValid,
        `Erdos64EG.Internal.runSurplusPairCT9_total,
        `Erdos64EG.Internal.surplusPairDecision,
        `Erdos64EG.Internal.surplusPairOfTwoLeSigma_distinct,
        `Erdos64EG.Internal.runSurplusPairCT9_checks_linear
      ]
    },
    {
      stageId := "proof-slice.high-center-structure"
      title := "CT1 four-cycle avoidance"
      summary := "The exact length-four target-avoiding run yields the reusable high-neighbourhood matching and no-common-neighbour consequences."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedHighCenterStructurePrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.runFourCycleAvoidingCT1_terminal,
        `Erdos64EG.Internal.runFourCycleAvoidingCT1_trace,
        `Erdos64EG.Internal.runFourCycleAvoidingCT1_total,
        `Erdos64EG.Internal.highCenter_neighborhood_matching,
        `Erdos64EG.Internal.highCenter_nonadjacent_noCommonOutside
      ]
    },
    {
      stageId := "proof-slice.port-classification"
      title := "CT10 selected-port classification"
      summary := "The canonical degree-surplus slots are classified as open or triangular from their two actual shoulders, with an exact missing/exhaustive state split."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSurplusPortClassificationPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.surplusPortClassification_stateSpace,
        `Erdos64EG.Internal.runSurplusPortClassificationCT10_checks_quadratic,
        `StructuralExhaustion.Graph.SurplusPortActivity.shoulderVertices_length
      ]
    },
    {
      stageId := "proof-slice.open-port-pairs"
      title := "CT9 open ports by centre"
      summary := "Capacity-one centre fibres return two distinct open selected ports at one centre or certify at most one at every centre; pairs are not enumerated."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedOpenPortPairPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.openPortPairDecision,
        `Erdos64EG.Internal.runOpenPortPairCT9_checks_cubic,
        `StructuralExhaustion.Graph.SurplusPortActivity.openPairDecision
      ]
    },
    {
      stageId := "proof-slice.open-port-responses"
      title := "Routed CT7 endpoint responses"
      summary := "Only an actual CT9 overload is routed to CT7; the bounded branch is preserved, while overload yields an adjacency-response distinction or complete neutrality."
      kind := .tactic
      tacticId? := some "CT7"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedOpenPortResponsePrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.openPortResponse_stateSpace,
        `StructuralExhaustion.Graph.OpenPortResponse.route_id,
        `StructuralExhaustion.Graph.AdjacencyResponse.checks_linear,
        `StructuralExhaustion.Routes.CT9ToCT7.routeContract
      ]
    },
    {
      stageId := "proof-slice.shoulder-ledger"
      title := "CT5 shoulder-pair ledger"
      summary := "One exact witness per selected port certifies its two non-centre shoulders; the charge ledger totals twice the selected-slot count."
      kind := .tactic
      tacticId? := some "CT5"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedPortShoulderLedgerPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.runPortShoulderLedgerCT5_terminal,
        `Erdos64EG.Internal.runPortShoulderLedgerCT5_total,
        `Erdos64EG.Internal.runPortShoulderLedgerCT5_checks_quadratic,
        `StructuralExhaustion.Graph.PortShoulderLedger.run_trace_charge
      ]
    },
    {
      stageId := "proof-slice.open-port-compatibility"
      title := "CT7 open-pair compatibility interpretation"
      summary := "An actual same-centre overload pair retains the routed CT7 certificate; four-cycle avoidance then separates endpoint adjacency from the exact fan-compatible shoulder conditions."
      kind := .tactic
      tacticId? := some "CT7"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedOpenPortCompatibilityPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.openPortCompatibility_stateSpace,
        `StructuralExhaustion.Graph.OpenPortCompatibility.stateSpace,
        `StructuralExhaustion.Graph.OpenPortCompatibility.fanCompatible_of_nonadjacent,
        `StructuralExhaustion.Graph.SurplusPortActivity.portEndpoint_injective_of_sameCenter
      ]
    },
    {
      stageId := "proof-slice.high-center-port-dichotomy"
      title := "CT10 all-port local dichotomy"
      summary := "At every high centre, CT10 classifies exactly the declared incident ports; matching neighbourhoods yield a fan-compatible open pair or at least degree-minus-two triangular ports."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedHighCenterPortDichotomyPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.highCenterPort_stage,
        `StructuralExhaustion.Graph.HighCenterPort.verifiedStage,
        `StructuralExhaustion.Graph.HighCenterPort.localDichotomy,
        `StructuralExhaustion.Graph.HighCenterPort.classificationChecks_linear
      ]
    },
    {
      stageId := "proof-slice.triangular-shoulder-completion"
      title := "CT5 triangular shoulder completions"
      summary := "Each shoulder of every actual triangular port has a completion incidence; central uniqueness and forbidden noncentral centre-neighbour endpoints are proved structurally."
      kind := .tactic
      tacticId? := some "CT5"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTriangularShoulderCompletionPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.triangularShoulder_stage,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.verifiedStage,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.exists_completion,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.not_both_shoulders_central,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.completion_eq_center_of_central,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.completion_not_other_center_neighbor,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.checks_quadratic
      ]
    },
    {
      stageId := "proof-slice.bridge-contraction"
      title := "CT2 bridge-contraction reduction"
      summary := "A hypothetical bridge is contracted structurally; one fewer vertex, preserved minimum degree, and exact same-length cycle lifting feed the constant-work CT2 contradiction."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedBridgeReductionPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.dart_not_bridge,
        `StructuralExhaustion.Graph.BridgeContraction.preserves_minDegree,
        `StructuralExhaustion.Graph.BridgeContraction.hasCycleWithLength_of_contraction,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeCT2Run_total,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeCT2Run_checks
      ]
    },
    {
      stageId := "proof-slice.triangular-port-return"
      title := "CT1 triangular-port return"
      summary := "The framework turns the verified non-bridge edge into one simple deleted-edge return, derives the shoulder path and exact cycle arithmetic, and checks the proof-carrying certificate once."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTriangularPortReturnPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DartReturn.ofNotBridge,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.BridgeReductionStage.dartReturn,
        `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.endpoint_not_mem_path,
        `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.cycle_isCycle,
        `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.cycle_length,
        `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.landingAlternative,
        `Erdos64EG.Internal.triangularPortReturn_length_ne,
        `Erdos64EG.Internal.triangularPortReturnStage
      ]
    },
    {
      stageId := "proof-slice.triangular-first-landing"
      title := "CT10 triangular first-landings"
      summary := "CT10 classifies the exact finite table of actual shoulder-completion incidences as central, cross-triangular, or outside and composes that result with the preceding CT1 return."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTriangularFirstLandingPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.TriangularFirstLanding.landing_exhaustive,
        `StructuralExhaustion.Graph.TriangularFirstLanding.classOf_sound,
        `StructuralExhaustion.Graph.TriangularFirstLanding.run_traceValid,
        `StructuralExhaustion.Graph.TriangularFirstLanding.run_total,
        `StructuralExhaustion.Graph.TriangularFirstLanding.checks_quadratic,
        `StructuralExhaustion.Graph.TriangularFirstLanding.classifyReturn,
        `Erdos64EG.Internal.triangularPortReturn_classified
      ]
    },
    {
      stageId := "proof-slice.triangular-cross-shoulder"
      title := "CT9 cross-shoulder multiplicity"
      summary := "CT9 scans the at-most-four cross-shoulder edges between two triangular ports; overload forces a high shoulder, while the surviving fibre has capacity one."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTriangularCrossShoulderPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.TriangularCrossShoulder.endpoint_nonadjacent,
        `StructuralExhaustion.Graph.TriangularCrossShoulder.shoulder_pairs_disjoint,
        `StructuralExhaustion.Graph.TriangularCrossShoulder.highShoulder_of_two,
        `StructuralExhaustion.Graph.TriangularCrossShoulder.stateSpace,
        `StructuralExhaustion.Graph.TriangularCrossShoulder.boundedRunOfCubic,
        `StructuralExhaustion.Graph.TriangularCrossShoulder.checks_constant,
        `Erdos64EG.Internal.triangularCrossShoulder_stateSpace
      ]
    },
    {
      stageId := "proof-slice.fan-closed-port"
      title := "CT5 fan-closed compatible ports"
      summary := "CT5 audits exactly four assigned oriented incidences of two compatible open ports; the graph layer derives both fan-closure conclusions and carrier distinctness."
      kind := .tactic
      tacticId? := some "CT5"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedFanClosedPortPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.FanClosedPort.incidenceKind_exact,
        `StructuralExhaustion.Graph.FanClosedPort.first_fanClosed,
        `StructuralExhaustion.Graph.FanClosedPort.second_fanClosed,
        `StructuralExhaustion.Graph.FanClosedPort.carriers_nodup,
        `StructuralExhaustion.Graph.FanClosedPort.verifiedStage,
        `Erdos64EG.Internal.p13FanWindowProfile,
        `Erdos64EG.Internal.fanClosedPairStage
      ]
    },
    {
      stageId := "proof-slice.fan-closed-mass"
      title := "CT14 cubic-closed fan mass"
      summary := "A registered CT5-to-CT14 route scans the actual cubic-closed-neighbour subtype, proves compatible-pair multiplicity at least two, and derives positive quarter deficit."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedFanClosedMassPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.CT5ToCT14.generated_route_id,
        `StructuralExhaustion.Graph.FanClosedPortMass.fanClosed_is_cubicClosed,
        `StructuralExhaustion.Graph.FanClosedPortMass.two_le_cubicClosed_card,
        `StructuralExhaustion.Graph.FanClosedPortMass.multiplicity_eq_card,
        `StructuralExhaustion.Graph.FanClosedPortMass.deficitNumerator_positive,
        `StructuralExhaustion.Graph.FanClosedPortMass.verifiedStage,
        `Erdos64EG.Internal.fanClosedMassStage
      ]
    },
    {
      stageId := "proof-slice.hybrid-fan-incidence"
      title := "CT14 hybrid fan-incidence budget"
      summary := "A registered CT14-to-CT14 refinement scans exactly two actual incidences per cubic-closed neighbour, proves endpoint disjointness and exact window/non-window multiplicities, and pays the positive deficit with three quarter-units of slack."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedHybridFanIncidencePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.CT14ToCT14.generated_route_id,
        `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card,
        `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card_le_twice_vertices,
        `StructuralExhaustion.Graph.HybridFanIncidence.other_injective,
        `StructuralExhaustion.Graph.HybridFanIncidence.multiplicity_partition,
        `StructuralExhaustion.Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack,
        `StructuralExhaustion.Graph.HybridFanIncidence.nonWindow_credit_pays_remaining,
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
        `Erdos64EG.Internal.hybridFanIncidenceStage
      ]
    },
    {
      stageId := "proof-slice.direct-fan-window"
      title := "CT1 direct fan-window elimination"
      summary := "Literal induced-path bridge constructors turn every failed same-window arithmetic clause into a simple power-of-two cycle; the selected avoiding branch is therefore direct-cycle-free with zero enumeration."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedDirectFanWindowPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathAttachment.mem_ambientSegment_support_bounds,
        `StructuralExhaustion.Graph.InducedPathBridge.connectorCycle,
        `StructuralExhaustion.Graph.InducedPathBridge.interlacingCycle,
        `StructuralExhaustion.Graph.FanWindowCycle.directCycleFree_iff,
        `StructuralExhaustion.Graph.FanWindowCycle.cycleOfViolation,
        `StructuralExhaustion.Graph.FanWindowCycle.verifiedAvoidingStage,
        `Erdos64EG.Internal.sameWindowPair_directCycleFree,
        `Erdos64EG.Internal.directFanWindowStage
      ]
    },
    {
      stageId := "proof-slice.two-window-cycle"
      title := "CT1 two-window cycle elimination"
      summary := "Two orientation-independent bridges through vertex-disjoint induced windows form a literal simple cycle of length 4+|i-j|+|a-b|; target avoidance excludes every accepted total with zero enumeration."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTwoWindowCyclePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathBridge.unorderedBridge,
        `StructuralExhaustion.Graph.InducedPathBridge.unorderedBridge_tail_member,
        `StructuralExhaustion.Graph.TwoWindowCycle.cycle,
        `StructuralExhaustion.Graph.TwoWindowCycle.directCycleFree_of_avoids,
        `StructuralExhaustion.Graph.TwoWindowCycle.verifiedAvoidingStage,
        `Erdos64EG.Internal.packedTwoWindow_directCycleFree,
        `Erdos64EG.Internal.twoWindowCycleStage
      ]
    },
    {
      stageId := "proof-slice.fan-label-packing"
      title := "CT9 certificate-marked fan degree cap"
      summary := "A legal pairwise-compatible label map on the actual fan ports has an injective eight-slot representative labelling, so the exact bounded CT9 execution proves degree at most eight without enumerating label codes or label families."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedFanLabelPackingPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.CT9.fibreCount_le_one_of_label_injective_on_items,
        `StructuralExhaustion.CT9.runBoundedOfLabelInjectiveOnItems,
        `StructuralExhaustion.Graph.P13PositionPacking.eq_or_positionDistance_eq_four_of_slot_eq,
        `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.run,
        `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.cardinality_le_eight,
        `Erdos64EG.Internal.MarkedFan.packingProfile,
        `Erdos64EG.Internal.MarkedFan.run,
        `Erdos64EG.Internal.MarkedFan.degree_le_eight
      ]
    },
    {
      stageId := "proof-slice.marked-fan-label-packing"
      title := "CT9 non-singleton marked-fan cap"
      summary := "Two positions in one marked label block two representative slots. A second bounded CT9 run on the erased port list leaves total capacity six and proves the original fan has degree at most seven."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedMarkedFanLabelPackingPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.CT9.runBoundedOfBounded,
        `StructuralExhaustion.CT9.fibreCount_eq_zero_of_label_absent,
        `StructuralExhaustion.Graph.P13PositionPacking.secondSlot_blocked,
        `StructuralExhaustion.Graph.P13PositionPacking.sum_twoBlockedCapacity_eq_six,
        `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.run,
        `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.cardinality_le_seven,
        `Erdos64EG.Internal.NonSingletonMarkedFan.packingProfile,
        `Erdos64EG.Internal.NonSingletonMarkedFan.run,
        `Erdos64EG.Internal.NonSingletonMarkedFan.degree_le_seven
      ]
    },
    {
      stageId := "proof-slice.certificate-closed-fan-charge"
      title := "CT14 certificate-closed fan charge"
      summary := "CT14 scans the actual fan ports, computes the cubic-closed count, and verifies the exact quarter-charge identity 11-k-4c. The defining condition 4c+k≤11 yields nonnegative closed-neighbourhood charge."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedCertificateClosedFanChargePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.closedCount_le_card,
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.count_partition,
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.run,
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.run_terminal,
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower_eq,
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower_nonnegative,
        `StructuralExhaustion.Graph.AssignedFanCharge.cubicClosed_iff_both_assigned,
        `StructuralExhaustion.Graph.AssignedFanCharge.quarterCharge_eq_neg_one_of_cubicClosed,
        `StructuralExhaustion.Graph.AssignedFanCharge.quarterCharge_ge_three_of_not_cubicClosed,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.chargeProfile,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.stage,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.chargeExact,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.charge_nonnegative
      ]
    },
    {
      stageId := "proof-slice.positive-deficit-fan-entry"
      title := "CT14 positive-deficit marked-fan entry"
      summary := "Two actual compatible fan-closed ports force at least two cubic-closed neighbours. The previously proved marked-fan cap supplies k≤8, and the routed CT14 incidence ledger pays the resulting positive quarter-deficit with three units of slack."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedPositiveDeficitFanEntryPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.massStage,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.degree_le_eight,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.two_le_closedCount,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.positiveDeficit,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybridStage,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_terminal,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays
      ]
    },
    {
      stageId := "proof-slice.local-b1-entry"
      title := "CT14 local hybrid B1 entry"
      summary := "The verified incidence execution projects to the exact semantic B1 ledger: 2c endpoint-disjoint carriers, an exact window/non-window partition, and payment of both the total deficit and the remaining non-window demand."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedLocalB1Prefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HybridFanIncidence.VerifiedStage.toLocalLedgerEntry,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1Entry,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1_endpoint_disjoint,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1_nonWindow_credit_pays
      ]
    },
    {
      stageId := "proof-slice.positive-deficit-candidate"
      title := "Concrete positive-deficit Type B candidate fibre"
      summary := "The framework candidate fibre is generated from the literal 2c fan incidences: every window incidence is mandatory, reserve-used incidences are forbidden, and selected non-window incidences must pay the exact remaining CT14 demand."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedPositiveDeficitCandidatePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.finite_candidate_fibre,
        `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.contains_every_window,
        `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.selected_reserve_free,
        `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.nonWindow_payment,
        `StructuralExhaustion.Graph.HybridFanCandidate.allItemsCandidate,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.reserveFreeCandidate
      ]
    },
    {
      stageId := "proof-slice.certificate-closed-candidate"
      title := "Concrete certificate-closed Type B candidate fibre"
      summary := "The candidate items are the actual fan-neighbour ports. Their assigned-incidence quarter weight is a proved lower bound for induced-core charge; an exact external-shoulder correction accounts for decorative and window incidences. Reserve-used vertices are forbidden, and validity is nonnegative center-plus-selected-neighbour lower-bound charge."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBCandidateFibresPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItems_weight_ge,
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.Candidate.charge_nonnegative,
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.Candidate.selected_reserve_free,
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_adjacent,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_endpoint_cubic,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_endpoint_not_high,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.reserveFreeCandidate
      ]
    },
    {
      stageId := "proof-slice.type-b-demand-system"
      title := "Derived dependent Type B demand system"
      summary := "Each declared center carries exactly one already verified local branch. The framework derives the heterogeneous item type, candidate subtype, finiteness proof, carrier support, and declared overlap universe; the application supplies none of those as certificate fields."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBDemandSystemPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.DependentWeightedSelection.Profile.refinedLedger,
        `Erdos64EG.Internal.TypeBAssignedSupport.candidateFamily,
        `Erdos64EG.Internal.TypeBAssignedSupport.candidate_finite,
        `Erdos64EG.Internal.TypeBAssignedSupport.demand_card_le_vertices,
        `Erdos64EG.Internal.TypeBAssignedSupport.demand_center_mem_declaredSupport
      ]
    },
    {
      stageId := "proof-slice.type-b-completion"
      title := "Unconditional CT12 choice-or-obstruction"
      summary := "CT12 consumes the complete declared center schedule. Empty schedules have the vacuous choice; otherwise Lean proves either a pairwise-disjoint full choice or a nonempty inclusion-minimal overlap obstruction, in at most one iteration per graph vertex."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedTypeBCompletionPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.fullChoice_or_obstruction,
        `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.exists_minimal_obstruction,
        `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.fullChoice_or_minimal_obstruction,
        `Erdos64EG.Internal.TypeBAssignedSupport.full_choice_or_minimal_obstruction,
        `Erdos64EG.Internal.TypeBAssignedSupport.completion_iterations_le_vertices
      ]
    },
    {
      stageId := "proof-slice.type-b-overlap"
      title := "Exact minimal Type B overlap support"
      summary := "Failure of the full choice produces a proof-carrying minimal obstruction. Its support uses every selected demand's declared carrier universe, so empty candidate fibres remain visible; target avoidance, high-center separation, cubic neighbours, and proper-subfamily choices are derived theorems."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBOverlapSupportPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.declaredCarrierSupport,
        `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.carrierSupport_subset_declared,
        `Erdos64EG.Internal.TypeBAssignedSupport.minimalOverlap_of_no_fullChoice,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.center_mem_carrierSet,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.ambient_dyadic_safe,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.centers_not_adjacent,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.center_neighbor_cubic,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.sameWindow_directCycleFree,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.twoWindow_directCycleFree,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_compression_impossible,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_separated_carrier_partition,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_subschedule_has_choice
      ]
    },
    {
      stageId := "proof-slice.type-b-resolution"
      title := "Graph-derived high-center resolution split"
      summary := "For a literal Type B vertex scope, the demand set is all ambient high centers in that scope. Proof-level finite resolution gives an exact trichotomy: an actual center has no verified local entry, or every center resolves and CT12 gives a full disjoint choice, or CT12 gives a minimal overlap obstruction."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBResolutionPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteResolution.Profile.fullResolution_or_unresolved,
        `Erdos64EG.Internal.TypeBSupportScope.highCenters,
        `Erdos64EG.Internal.TypeBSupportScope.center_high,
        `Erdos64EG.Internal.TypeBSupportScope.assignedSupport,
        `Erdos64EG.Internal.TypeBSupportScope.unresolved_or_fullChoice_or_minimalOverlap
      ]
    },
    {
      stageId := "proof-slice.type-b-assigned-charge"
      title := "Exact assigned charge, receiver discharge, and boundary split"
      summary := "Lean transfers every candidate weight and half-credit to literal induced-core charge and proves the exact post-selection decomposition. Independently of local resolution or B2 disjointness, deleting all actual high centers leaves a literal P13-free, core-free, subcubic graph. Its exact receiver overload gives the unconditional bound -TypeBNet ≤ 21 assigned-surplus + TypeA-overload."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBPostLedgerPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.Choice.refinedSupport_pairwiseDisjoint,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.coreQuarterCharge_eq_used_add_centers_add_remaining,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.centerCoreCharge_add_card_nonnegative,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.netQuarterCharge_nonnegative_or_remaining_negative,
        `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.quarterCharge_nonnegative,
        `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.neg_quarterCharge_le_totalOverload,
        `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.saturated_or_unsaturated,
        `StructuralExhaustion.Core.FiniteBoundaryTransfer.Profile.transfer_or_overloaded,
        `StructuralExhaustion.Graph.LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver,
        `StructuralExhaustion.Graph.FiniteInducedBoundary.Profile.exists_incidence_of_loss_pos,
        `StructuralExhaustion.Graph.HighCenterDeletionCharge.Profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload,
        `StructuralExhaustion.Graph.WindowExternalCharge.windowQuarterCredit_le_externalCorrection,
        `StructuralExhaustion.Graph.InducedCoreFanReserve.incidence_free_ordinary_of_nonWindow,
        `Erdos64EG.Internal.TypeBAssignedSupport.actualCoreSupport_subset_carrierSupport,
        `Erdos64EG.Internal.TypeBAssignedSupport.fullActualCoreSupport_pairwiseDisjoint,
        `Erdos64EG.Internal.TypeBAssignedSupport.fullLocalQuarterBalance_le_actualCharge,
        `Erdos64EG.Internal.TypeBAssignedSupport.processedFanCharge_nonnegative,
        `Erdos64EG.Internal.TypeBAssignedSupport.netQuarterCharge_nonnegative_or_remaining_negative,
        `Erdos64EG.Internal.TypeBAssignedSupport.remainingInducedQuarterCharge_eq_raw_add_boundary,
        `Erdos64EG.Internal.TypeBAssignedSupport.netQuarterCharge_nonnegative_of_unsaturated_boundaryTransfer,
        `Erdos64EG.Internal.TypeBAssignedSupport.boundaryOverload_has_landing,
        `Erdos64EG.Internal.TypeBLocalEntry.actualCoreSupport_card_le_twentyFour,
        `Erdos64EG.Internal.TypeBAssignedSupport.processedDegreeSum_le_twoHundred_mul_centers,
        `Erdos64EG.Internal.TypeBAssignedSupport.neg_netQuarterCharge_le_eightHundred_mul_assignedSurplus_of_unsaturated,
        `Erdos64EG.Internal.TypeBSupportScope.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_receiverOverload,
        `Erdos64EG.Internal.TypeBSupportScope.unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload
      ]
    },
    {
      stageId := "proof-slice.sparse-envelope"
      title := "CT12 two-degenerate sparse envelope"
      summary := "Deletion criticality supplies a cubic vertex. The no-proper-core theorem makes its literal complement 2-degenerate; CT12 audits the proof-selected elimination list exactly once per remaining vertex, yielding m ≤ 2n-2 and the exact sparse slack/surplus identities."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSparseEnvelopePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DegeneracyPeeling.exists_certificate_of_internalMinDegreeFree,
        `StructuralExhaustion.Graph.DegeneracyPeeling.edgeCount_le_two_mul_vertexCount_sub_three,
        `StructuralExhaustion.Graph.DegeneracyPeeling.Profile.verifiedStage,
        `StructuralExhaustion.Graph.SurplusPortActivity.degreeExcess_sum_int_eq,
        `Erdos64EG.Internal.sparseEnvelopeProfile,
        `Erdos64EG.Internal.sparseEnvelopeRoot_degree,
        `Erdos64EG.Internal.sparseEnvelopeRemaining_coreFree,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_terminal,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_trace,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_verified,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_traceValid,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_total,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_iterations,
        `Erdos64EG.Internal.runSparseEnvelopeCT12_linearBudget,
        `Erdos64EG.Internal.sparseEnvelopeRemaining_edgeBound,
        `Erdos64EG.Internal.sparseEnvelope_edgeBound,
        `Erdos64EG.Internal.sparseSlack_surplus_identity,
        `Erdos64EG.Internal.sparseEdge_surplus_identity,
        `Erdos64EG.Internal.sparseSurplus_eq_degreeExcessLedger
      ]
    }
  ]
  links := [
    {
      linkId := "proof-slice.official-internal"
      sourceStageId := "proof-slice.official"
      targetStageId := "proof-slice.internal"
      kind := .frameworkComposition
      label := "faithful executable boundary"
      description := "The internal target is proved equivalent to the exact conclusion of the official formulation and is the statement boundary used by the verified prefix."
      evidenceDeclarations := [`Erdos64EG.Internal.target_iff_official_conclusion]
    },
    {
      linkId := "proof-slice.internal-fixture"
      sourceStageId := "proof-slice.internal"
      targetStageId := "proof-slice.k4-fixture"
      kind := .sharedProblem
      label := "closed smoke fixture"
      description := "K₄ instantiates the internal finite-object interface and carries one explicit accepted cycle."
    },
    {
      linkId := "proof-slice.fixture-ct1"
      sourceStageId := "proof-slice.k4-fixture"
      targetStageId := "proof-slice.ct1"
      kind := .validation
      label := "validate rooted return"
      description := "CT1 validates the rooted return obtained from the supplied K₄ cycle."
    },
    {
      linkId := "proof-slice.ct1-no-proper-core"
      sourceStageId := "proof-slice.ct1"
      targetStageId := "proof-slice.no-proper-core"
      kind := .frameworkComposition
      label := "lexicographic certified reduction"
      description := "The packed graph profile retains the target-avoiding branch, selects the lexicographically minimal counterexample by natural-number well-ordering, and executes one supplied proper-subgraph reduction."
      automationDeclarations := [
        `StructuralExhaustion.CT2.runCertifiedReduction
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.CT2.runCertifiedReduction,
        `Erdos64EG.Internal.exists_verifiedNoProperCorePrefix
      ]
    },
    {
      linkId := "proof-slice.no-proper-core-ct2"
      sourceStageId := "proof-slice.no-proper-core"
      targetStageId := "proof-slice.ct2"
      kind := .frameworkComposition
      label := "same selected graph"
      description := "The node [8] output contains the existing edge-rooted CT1 and local dart-deletion CT2 prefix on its fixed exposed vertex type."
      evidenceDeclarations := [
        `Erdos64EG.Internal.noProperCorePrefix_previous,
        `Erdos64EG.Internal.localRoute_disabled
      ]
    },
    {
      linkId := "proof-slice.ct2-ct3"
      sourceStageId := "proof-slice.ct2"
      targetStageId := "proof-slice.ct3"
      kind := .frameworkComposition
      label := "same packed minimal context"
      description := "The Erdős instantiation retains the exact CT1/CT2 prefix on its selected graph and adds the framework's literal CT3 replacement stage."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedBoundariedReplacementPrefix,
        `Erdos64EG.Internal.boundariedReplacementPrefix_previous,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
      ]
    },
    {
      linkId := "proof-slice.ct3-induced-p13"
      sourceStageId := "proof-slice.ct3"
      targetStageId := "proof-slice.induced-p13"
      kind := .frameworkComposition
      label := "same packed minimal context"
      description := "The induced-path CT1 input is the inherited branch context of the exact CT3 prefix. The sole HSS external theorem closes its avoiding residual, and the graph profile retains the resulting C1 stage without reselecting the graph."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.verifiedInducedPathStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedInducedP13Prefix,
        `Erdos64EG.Internal.inducedP13Prefix_previous,
        `Erdos64EG.Internal.hssTarget_of_p13Free,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.verifiedInducedPathStage
      ]
    },
    {
      linkId := "proof-slice.induced-p13-packing"
      sourceStageId := "proof-slice.induced-p13"
      targetStageId := "proof-slice.p13-packing"
      kind := .registeredRoute
      label := "registered CT1→CT12 route"
      description := "The registered CT1 C1-to-CT12 route consumes the exact induced-path realization, derives nonemptiness of the selected maximum family, runs CT12 on that family, and retains the preceding prefix unchanged."
      routeId? := some "CT1.terminal.c1->CT12"
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT1ToCT12.routeContract
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13PackingPrefix,
        `Erdos64EG.Internal.p13PackingPrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingPrefix,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingRoute_id,
        `StructuralExhaustion.Routes.CT1ToCT12.routeContract
      ]
    },
    {
      linkId := "proof-slice.p13-packing-labels"
      sourceStageId := "proof-slice.p13-packing"
      targetStageId := "proof-slice.p13-labels"
      kind := .frameworkComposition
      label := "same selected graph and branch context"
      description := "The graph profile consumes the exact CT12 packing prefix unchanged, runs the complete finite label table in its inherited branch context, and proves every actual attachment label is accepted from target avoidance."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingAttachmentPrefix
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13LabelAlgebraPrefix,
        `Erdos64EG.Internal.p13LabelAlgebraPrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingAttachmentPrefix
      ]
    },
    {
      linkId := "proof-slice.labels-surplus-ct6"
      sourceStageId := "proof-slice.p13-labels"
      targetStageId := "proof-slice.surplus-ct6"
      kind := .frameworkComposition
      label := "same selected graph"
      description := "The Erdős layer retains the exact CT10 predecessor and supplies deletion criticality to the graph-owned ordered surplus profile."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivity.run
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedSparseSurplusPrefix,
        `Erdos64EG.Internal.VerifiedSparseSurplusPrefix.previous
      ]
    },
    {
      linkId := "proof-slice.surplus-ct6-pairs"
      sourceStageId := "proof-slice.surplus-ct6"
      targetStageId := "proof-slice.surplus-pairs"
      kind := .registeredRoute
      label := "registered CT6→CT9 route"
      description := "The framework route consumes the actual CT6 active-ledger residual, preserves the complete branch context, and supplies exactly the graph-owned surplus-slot collection to CT9."
      routeId? := some "CT6.residual.activeLedger->CT9"
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT6ToCT9.routeContract
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedSurplusPairPrefix,
        `Erdos64EG.Internal.VerifiedSurplusPairPrefix.previous,
        `Erdos64EG.Internal.surplusPairRoute_id,
        `Erdos64EG.Internal.surplusPairRoute_context_preserved,
        `StructuralExhaustion.Routes.CT6ToCT9.routeContract
      ]
    },
    {
      linkId := "proof-slice.surplus-pairs-high-center"
      sourceStageId := "proof-slice.surplus-pairs"
      targetStageId := "proof-slice.high-center-structure"
      kind := .sharedProblem
      label := "same selected graph"
      description := "The CT1 length-four avoiding certificate is derived from the inherited target-avoidance proof and retains the complete preceding prefix."
      automationDeclarations := [
        `StructuralExhaustion.Graph.HighCenterStructure.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedHighCenterStructurePrefix,
        `Erdos64EG.Internal.VerifiedHighCenterStructurePrefix.previous,
        `StructuralExhaustion.Graph.HighCenterStructure.verifiedStage
      ]
    },
    {
      linkId := "proof-slice.high-center-port-classification"
      sourceStageId := "proof-slice.high-center-structure"
      targetStageId := "proof-slice.port-classification"
      kind := .sharedProblem
      label := "graph-owned port data"
      description := "The reusable graph profile derives canonical endpoints and shoulders from the same graph and deletion-critical certificate, then runs CT10 on the explicit selected-slot list."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivity.verifiedClassificationStage
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivity.verifiedClassificationStage
      ]
    },
    {
      linkId := "proof-slice.port-classification-open-pairs"
      sourceStageId := "proof-slice.port-classification"
      targetStageId := "proof-slice.open-port-pairs"
      kind := .sharedProblem
      label := "open-slot subtype"
      description := "CT9 consumes the exact open selected-slot subtype and labels it by the already defined centre; no semantic route adapter or pair universe is required."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivity.verifiedOpenPairStage
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivity.verifiedOpenPairStage
      ]
    },
    {
      linkId := "proof-slice.open-pairs-responses"
      sourceStageId := "proof-slice.open-port-pairs"
      targetStageId := "proof-slice.open-port-responses"
      kind := .registeredRoute
      label := "registered CT9→CT7 route"
      description := "The framework route exists only for the CT9 overload residual, preserves the branch context, and maps its exact capacity-one pair to canonical port endpoints."
      routeId? := some "CT9.residual.overload->CT7"
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT9ToCT7.routeContract
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.CT9ToCT7.routeContract,
        `StructuralExhaustion.Graph.OpenPortResponse.route_id,
        `Erdos64EG.Internal.openPortResponse_stateSpace
      ]
    },
    {
      linkId := "proof-slice.responses-shoulder-ledger"
      sourceStageId := "proof-slice.open-port-responses"
      targetStageId := "proof-slice.shoulder-ledger"
      kind := .sharedProblem
      label := "same selected ports"
      description := "The CT5 graph profile reuses the canonical selected-slot family and deletion criticality to certify exactly two shoulders per slot, retaining the conditional CT7 state split unchanged."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PortShoulderLedger.verifiedStage
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.PortShoulderLedger.verifiedStage
      ]
    },
    {
      linkId := "proof-slice.shoulder-ledger-open-port-compatibility"
      sourceStageId := "proof-slice.shoulder-ledger"
      targetStageId := "proof-slice.open-port-compatibility"
      kind := .sharedProblem
      label := "four-cycle-free semantic refinement"
      description := "The framework interprets the exact CT9 overload pair already routed through CT7. It preserves the bounded branch and proves the manuscript's fan-compatibility predicate precisely when the two canonical endpoints are nonadjacent."
      automationDeclarations := [
        `StructuralExhaustion.Graph.OpenPortCompatibility.stateSpace
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.openPortCompatibility_stateSpace,
        `StructuralExhaustion.Graph.OpenPortCompatibility.stateSpace
      ]
    },
    {
      linkId := "proof-slice.open-port-compatibility-high-center-dichotomy"
      sourceStageId := "proof-slice.open-port-compatibility"
      targetStageId := "proof-slice.high-center-port-dichotomy"
      kind := .sharedProblem
      label := "all incident ports at the same graph"
      description := "The generic CT10 profile reuses deletion criticality and four-cycle avoidance, but scans all actual neighbours of one centre rather than only the selected excess slots."
      automationDeclarations := [
        `StructuralExhaustion.Graph.HighCenterPort.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.highCenterPort_stage,
        `StructuralExhaustion.Graph.HighCenterPort.verifiedStage
      ]
    },
    {
      linkId := "proof-slice.high-center-dichotomy-shoulder-completion"
      sourceStageId := "proof-slice.high-center-port-dichotomy"
      targetStageId := "proof-slice.triangular-shoulder-completion"
      kind := .sharedProblem
      label := "triangular-port shoulder sites"
      description := "The CT5 profile consumes the generic all-incident triangular-port subtype at the same centre and scans only its two shoulder sites against the declared vertex schedule."
      automationDeclarations := [
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.triangularShoulder_stage,
        `StructuralExhaustion.Graph.TriangularShoulderCompletion.verifiedStage
      ]
    },
    {
      linkId := "proof-slice.shoulder-completion-bridge-contraction"
      sourceStageId := "proof-slice.triangular-shoulder-completion"
      targetStageId := "proof-slice.bridge-contraction"
      kind := .sharedProblem
      label := "same selected minimal counterexample"
      description := "The reusable bridge reduction uses only the minimum-degree baseline, target avoidance, and packed minimality already retained on the identical graph; no triangular-port fact is assumed by the reduction."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeReductionStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.bridgeReductionStage,
        `Erdos64EG.Internal.dart_not_bridge
      ]
    },
    {
      linkId := "proof-slice.bridge-contraction-triangular-return"
      sourceStageId := "proof-slice.bridge-contraction"
      targetStageId := "proof-slice.triangular-port-return"
      kind := .frameworkComposition
      label := "non-bridge to proof-carrying return"
      description := "The framework consumes the CT2 bridgelessness theorem, obtains one simple path by Mathlib reachability, and feeds that exact certificate to CT1 without enumerating walks."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.BridgeReductionStage.dartReturn,
        `StructuralExhaustion.Graph.TriangularPortReturn.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.triangularPortRoot,
        `Erdos64EG.Internal.triangularPortReturnStage
      ]
    },
    {
      linkId := "proof-slice.triangular-return-first-landing"
      sourceStageId := "proof-slice.triangular-port-return"
      targetStageId := "proof-slice.triangular-first-landing"
      kind := .frameworkComposition
      label := "return completion to exact landing class"
      description := "The framework keeps the CT1 return certificate, embeds its first noncentral completion as a datum of the explicit CT10 table, and proves the central/cross/outside semantics without an application-local transition."
      automationDeclarations := [
        `StructuralExhaustion.Graph.TriangularFirstLanding.verifiedStage,
        `StructuralExhaustion.Graph.TriangularFirstLanding.classifyReturn
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.triangularPortReturn_classified
      ]
    },
    {
      linkId := "proof-slice.first-landing-cross-shoulder"
      sourceStageId := "proof-slice.triangular-first-landing"
      targetStageId := "proof-slice.triangular-cross-shoulder"
      kind := .sharedProblem
      label := "cross-triangular fibre on the same fan"
      description := "The graph-owned CT9 profile refines the cross-triangular landing class to the four literal shoulder pairs of two fixed ports and exposes the high-shoulder versus capacity-one split."
      automationDeclarations := [
        `StructuralExhaustion.Graph.TriangularCrossShoulder.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.triangularCrossShoulderStage,
        `Erdos64EG.Internal.triangularCrossShoulder_stateSpace
      ]
    },
    {
      linkId := "proof-slice.cross-shoulder-fan-closed"
      sourceStageId := "proof-slice.triangular-cross-shoulder"
      targetStageId := "proof-slice.fan-closed-port"
      kind := .sharedProblem
      label := "assigned compatible-pair ledger"
      description := "On the identical selected graph, the application supplies the literal P13 window complement and four Type-B assignment facts; the framework derives fan closure rather than accepting it as a certificate."
      automationDeclarations := [
        `StructuralExhaustion.Graph.FanClosedPort.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13FanWindowProfile,
        `Erdos64EG.Internal.fanClosedPairStage
      ]
    },
    {
      linkId := "proof-slice.fan-closed-mass"
      sourceStageId := "proof-slice.fan-closed-port"
      targetStageId := "proof-slice.fan-closed-mass"
      kind := .registeredRoute
      routeId? := some "CT5.residual.chargeLedger->CT14"
      label := "charge ledger to actual fan mass"
      description := "The framework extracts the actual CT5 charge residual, preserves the branch context, materializes CT14's empty trigger, and scans the semantic cubic-closed-neighbour subtype."
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT5ToCT14.routeContract,
        `StructuralExhaustion.Routes.CT5ToCT14.buildInput,
        `StructuralExhaustion.Routes.CT5ToCT14.generated_route_id
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.FanClosedPortMass.verifiedStage,
        `Erdos64EG.Internal.fanClosedMassStage
      ]
    },
    {
      linkId := "proof-slice.hybrid-fan-incidence"
      sourceStageId := "proof-slice.fan-closed-mass"
      targetStageId := "proof-slice.hybrid-fan-incidence"
      kind := .registeredRoute
      routeId? := some "CT14.residual.capacity->CT14"
      label := "mass capacity to incidence refinement"
      description := "The framework extracts the actual CT14 capacity residual, preserves the branch context, and runs a second CT14 capability over the two-per-member incidence universe."
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT14ToCT14.routeContract,
        `StructuralExhaustion.Routes.CT14ToCT14.buildInput,
        `StructuralExhaustion.Routes.CT14ToCT14.generated_route_id
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
        `Erdos64EG.Internal.hybridFanIncidenceStage
      ]
    },
    {
      linkId := "proof-slice.direct-fan-window"
      sourceStageId := "proof-slice.hybrid-fan-incidence"
      targetStageId := "proof-slice.direct-fan-window"
      kind := .frameworkComposition
      label := "literal attachment cycles"
      description := "The graph layer retains the same selected object and constructs the internal, centre-crossing, and interlacing cycle certificates from one closed-pair record; CT1 validates target avoidance without scanning any candidate universe."
      automationDeclarations := [
        `StructuralExhaustion.Graph.FanWindowCycle.verifiedAvoidingStage
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.FanWindowCycle.cycleOfViolation,
        `Erdos64EG.Internal.directFanWindowStage
      ]
    },
    {
      linkId := "proof-slice.two-window-cycle"
      sourceStageId := "proof-slice.direct-fan-window"
      targetStageId := "proof-slice.two-window-cycle"
      kind := .frameworkComposition
      label := "two disjoint window bridges"
      description := "The same selected graph and CT1 target encoding are retained. The graph layer follows one symbolic segment in each of two disjoint windows and proves the concatenated walk simple by support disjointness."
      automationDeclarations := [
        `StructuralExhaustion.Graph.TwoWindowCycle.verifiedAvoidingStage
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.TwoWindowCycle.cycle,
        `Erdos64EG.Internal.twoWindowCycleStage
      ]
    },
    {
      linkId := "proof-slice.fan-label-packing"
      sourceStageId := "proof-slice.two-window-cycle"
      targetStageId := "proof-slice.fan-label-packing"
      kind := .frameworkComposition
      label := "certificate-marked fan packing"
      description := "The marked-fan branch supplies only its legal pairwise-compatible label map on actual incident ports. The graph layer chooses representatives and CT9 owns the fixed eight-fibre capacity audit."
      automationDeclarations := [
        `StructuralExhaustion.CT9.runBoundedOfLabelInjectiveOnItems
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.cardinality_le_eight,
        `Erdos64EG.Internal.MarkedFan.degree_le_eight
      ]
    },
    {
      linkId := "proof-slice.marked-fan-label-packing"
      sourceStageId := "proof-slice.fan-label-packing"
      targetStageId := "proof-slice.marked-fan-label-packing"
      kind := .frameworkComposition
      label := "two blocked representative slots"
      description := "The graph layer erases the distinguished marked port, derives two zero-capacity slots from its two positions, and executes an ordinary CT9 bounded partition with six remaining slots."
      automationDeclarations := [
        `StructuralExhaustion.CT9.runBoundedOfBounded
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.cardinality_le_seven,
        `Erdos64EG.Internal.NonSingletonMarkedFan.degree_le_seven
      ]
    },
    {
      linkId := "proof-slice.certificate-closed-fan-charge"
      sourceStageId := "proof-slice.marked-fan-label-packing"
      targetStageId := "proof-slice.certificate-closed-fan-charge"
      kind := .frameworkComposition
      label := "exact marked-fan charge ledger"
      description := "On the same selected graph, the application supplies the literal assigned-incidence relation and the certificate-closed inequality. The graph layer computes assigned cubic closure and its exact assigned-incidence weight; CT14 owns the exact port scan. Transfer to induced-core charge is a separate proved correction theorem."
      automationDeclarations := [
        `StructuralExhaustion.CT14.run_terminal_capacity_of_complete
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower_nonnegative,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.charge_nonnegative
      ]
    },
    {
      linkId := "proof-slice.positive-deficit-fan-entry"
      sourceStageId := "proof-slice.certificate-closed-fan-charge"
      targetStageId := "proof-slice.positive-deficit-fan-entry"
      kind := .frameworkComposition
      label := "marked cap to positive hybrid entry"
      description := "The same selected graph retains the marked-fan CT9 cap. The framework-owned CT5-to-CT14 mass stage and CT14-to-CT14 incidence refinement consume literal assigned fan-closed data and derive the positive deficit and paying capacity."
      automationDeclarations := [
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybridStage
      ]
    },
    {
      linkId := "proof-slice.local-b1-entry"
      sourceStageId := "proof-slice.positive-deficit-fan-entry"
      targetStageId := "proof-slice.local-b1-entry"
      kind := .frameworkComposition
      label := "verified CT14 stage realizes local B1"
      description := "The framework forgets only execution bookkeeping and retains the exact carrier disjointness, binary multiplicity partition, total-credit payment, and remaining non-window payment used by the manuscript B1 statement."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HybridFanIncidence.VerifiedStage.toLocalLedgerEntry,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1Entry
      ]
    },
    {
      linkId := "proof-slice.positive-deficit-candidate"
      sourceStageId := "proof-slice.local-b1-entry"
      targetStageId := "proof-slice.positive-deficit-candidate"
      kind := .frameworkComposition
      label := "literal B1 incidences generate the candidate fibre"
      description := "The graph layer turns the already verified incidence universe and remaining-payment inequality into the exact mandatory/forbidden/weighted candidate predicate. The Erdős declaration only supplies its fixed fan profile and reserve."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HybridFanCandidate.allItems_weight_eq_nonWindowQuarterCredit,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.candidate_nonWindow_payment
      ]
    },
    {
      linkId := "proof-slice.certificate-closed-candidate"
      sourceStageId := "proof-slice.positive-deficit-candidate"
      targetStageId := "proof-slice.certificate-closed-candidate"
      kind := .frameworkComposition
      label := "the other Type B local branch gets a literal fibre"
      description := "The framework reuses the exact CT14 closed/open count and charge identity to define the certificate-closed weighted subset. Deletion criticality proves selected neighbours are cubic and therefore outside the high-center set."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate,
        `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_endpoint_not_high
      ]
    },
    {
      linkId := "proof-slice.type-b-demand-system"
      sourceStageId := "proof-slice.certificate-closed-candidate"
      targetStageId := "proof-slice.type-b-demand-system"
      kind := .frameworkComposition
      label := "local fibres form one dependent ledger"
      description := "The common dependent weighted-selection adapter derives the CT12 candidate and support fields from the two literal local selection profiles."
      evidenceDeclarations := [
        `StructuralExhaustion.Core.DependentWeightedSelection.Profile.refinedLedger,
        `Erdos64EG.Internal.TypeBAssignedSupport.ledgerProfile
      ]
    },
    {
      linkId := "proof-slice.type-b-completion"
      sourceStageId := "proof-slice.type-b-demand-system"
      targetStageId := "proof-slice.type-b-completion"
      kind := .frameworkComposition
      label := "execute CT12 on the declared schedule"
      description := "The unconditional refined-ledger theorem handles empty and nonempty schedules without enumerating candidate products or demand subsets."
      automationDeclarations := [
        `StructuralExhaustion.CT12.RefinedLedgerCompletion.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBAssignedSupport.completionStage
      ]
    },
    {
      linkId := "proof-slice.type-b-overlap"
      sourceStageId := "proof-slice.type-b-completion"
      targetStageId := "proof-slice.type-b-overlap"
      kind := .frameworkComposition
      label := "contrapositive B2 failure"
      description := "Negating the full disjoint choice selects the minimal-obstruction side. Declared demand supports preserve reserve-blocked centers and all proper shorter subfamilies have choices."
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBAssignedSupport.minimalOverlap_of_no_fullChoice,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_disjoint_choice
      ]
    },
    {
      linkId := "proof-slice.type-b-resolution"
      sourceStageId := "proof-slice.type-b-overlap"
      targetStageId := "proof-slice.type-b-resolution"
      kind := .frameworkComposition
      label := "derive the complete high-center schedule"
      description := "The application now starts from a vertex scope rather than a supplied center list. Every high center either lacks the verified local data explicitly or participates in the complete CT12 family."
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBSupportScope.unresolved_or_fullChoice_or_minimalOverlap
      ]
    },
    {
      linkId := "proof-slice.type-b-assigned-charge"
      sourceStageId := "proof-slice.type-b-completion"
      targetStageId := "proof-slice.type-b-assigned-charge"
      kind := .frameworkComposition
      label := "realize the disjoint choice in actual graph charge"
      description := "The framework transports candidate-carrier disjointness to the literal induced-core supports used by the local proofs. The exact post-selection graph ledger then yields nonnegative net charge or a strictly negative remaining core."
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.Choice.refinedSupport_pairwiseDisjoint,
        `Erdos64EG.Internal.TypeBAssignedSupport.fullLocalQuarterBalance_le_actualCharge,
        `Erdos64EG.Internal.TypeBAssignedSupport.netQuarterCharge_nonnegative_or_remaining_negative
      ]
    },
    {
      linkId := "proof-slice.sparse-envelope"
      sourceStageId := "proof-slice.type-b-assigned-charge"
      targetStageId := "proof-slice.sparse-envelope"
      kind := .frameworkComposition
      label := "same selected minimal graph"
      description := "The retained packed context already contains deletion criticality and the no-proper-core theorem. The graph profile converts those exact outputs into one bounded elimination certificate and CT12 executes its finite list."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DegeneracyPeeling.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.sparseEnvelopeProfile,
        `Erdos64EG.Internal.sparseEnvelope_edgeBound,
        `Erdos64EG.Internal.exists_verifiedSparseEnvelopePrefix
      ]
    }
  ]
}

private def erdosManuscript : ExampleManuscriptDescriptor := {
  title := "Erdős--Gyárfás Problem 64 proof"
  path := "proofs/erdos_64_eg/erdos_64_proof.tex"
  proofSteps := [
    {
      stepId := "erdos.official"
      stageId? := some "proof-slice.official"
      title := "Official theorem boundary"
      plainExplanation :=
        "The public Lean proposition uses the same finite simple graph and asks for exactly the power-of-two cycle asserted by the manuscript's main theorem."
      formalStatement :=
        "\\delta(G) \\ge 3 \\Longrightarrow \\exists k \\ge 2,\\ \\exists C \\subseteq G,\\ |C|=2^k"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "thm:main", title := "Main closure", nodeIds := [1, 2, 3] }
      ]
      declarationGroups := [
        {
          groupId := "official-statement"
          title := "Public mathematical statement"
          role := .mathematicalDefinition
          explanation :=
            "This declaration is the exact Mathlib-facing proposition that the completed formalization must prove."
          declarations := [`Erdos64EG.OfficialStatement]
        }
      ]
      scopeNotes :=
        "The public statement is exact, but the current verified workflow is explicitly a partial prefix and does not yet prove this proposition."
      workBound := "Statement boundary only; no computation is performed."
    },
    {
      stepId := "erdos.internal-boundary"
      stageId? := some "proof-slice.internal"
      title := "Faithful executable target"
      plainExplanation :=
        "Lean equips the same Mathlib graph with finite inspection data and replaces the unbounded exponent quantifier by a bounded decidable search, then proves that this executable target is equivalent to the official conclusion."
      formalStatement :=
        "\\operatorname{Target}(G) \\iff \\exists k \\ge 2,\\ \\exists C \\subseteq G,\\ |C|=2^k"
      status := .implemented
      correspondence := .equivalentEncoding
      manuscriptRefs := [
        { label := "thm:main", title := "Main closure", nodeIds := [1, 2, 3, 4] }
      ]
      declarationGroups := [
        {
          groupId := "executable-boundary"
          title := "Encoding and equivalence bridge"
          role := .encodingBridge
          explanation :=
            "The static input supplies deterministic finite data; the two equivalence theorems prove that neither the cycle predicate nor its exponent range has changed."
          declarations := [
            `Erdos64EG.Internal.staticInput,
            `Erdos64EG.Internal.powerOfTwoLength_iff,
            `Erdos64EG.Internal.target_iff_official_conclusion
          ]
        }
      ]
      scopeNotes :=
        "Finite enumeration and adjacency decisions control execution order only; they do not introduce a second graph representation or weaken the theorem."
      workBound := "The exponent search is bounded by the candidate cycle length."
    },
    {
      stepId := "erdos.k4-fixture"
      stageId? := some "proof-slice.k4-fixture"
      title := "Concrete K₄ execution fixture"
      plainExplanation :=
        "A four-cycle in K₄ is converted into a length-three return after deleting its root edge, providing a closed smoke test for the target encoding and CT1 execution."
      formalStatement :=
        "C_4 \\subseteq K_4 \\quad\\Longleftrightarrow\\quad 3 \\in R_e(K_4)"
      status := .implemented
      correspondence := .support
      declarationGroups := [
        {
          groupId := "k4-certificate"
          title := "Concrete certificate and checks"
          role := .fixture
          explanation :=
            "These declarations construct K₄, prove its baseline and four-cycle facts, and pin the corresponding Mersenne-return certificate. They test the general implementation but are not used as proof of the general theorem."
          declarations := [
            `Erdos64EG.Tests.k4Cycle,
            `Erdos64EG.Tests.k4_baseline,
            `Erdos64EG.Tests.fourCycleWalk_isCycle,
            `Erdos64EG.Tests.fourCycleWalk_powerOfTwo,
            `Erdos64EG.Tests.k4MersenneReturn
          ]
        }
      ]
      scopeNotes :=
        "This is implementation support rather than a manuscript proof step; no general claim is inferred from K₄."
      workBound := "One fixed four-vertex certificate."
    },
    {
      stepId := "erdos.mersenne-target"
      stageId? := some "proof-slice.ct1"
      title := "Mersenne return target algebra"
      plainExplanation :=
        "Removing one edge from a power-of-two cycle leaves a return path whose length is one less than a power of two. Conversely, adjoining the root edge to such a return produces the target cycle. CT1 records either a supplied return or universal avoidance."
      formalStatement :=
        "G \\text{ has a } C_{2^j} \\iff \\exists e,\\ 2^j-1 \\in R_e(G)"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "def:mersenne-return-set", title := "Mersenne return set", nodeIds := [5] },
        { label := "lem:return-equivalence", title := "Edge-rooted target equivalence", nodeIds := [5, 6, 7] }
      ]
      declarationGroups := [
        {
          groupId := "target-semantics"
          title := "Exact graph-theoretic equivalences"
          role := .semanticTheorem
          explanation :=
            "These theorems identify the internal target with existence of a Mersenne return and identify target avoidance with disjointness of every return set from the Mersenne lengths."
          declarations := [
            `Erdos64EG.Internal.target_iff_hasMersenneReturn,
            `Erdos64EG.Internal.not_target_iff_returnSets_disjoint
          ]
        },
        {
          groupId := "ct1-executions"
          title := "Positive and avoiding CT1 executions"
          role := .tacticExecution
          explanation :=
            "The positive run validates one proof-carrying return; the avoiding run retains the exact universal non-realization residual. The K₄ run pins the positive path on a concrete input."
          declarations := [
            `Erdos64EG.Internal.runAvoidingCT1,
            `Erdos64EG.Internal.runMersenneCT1,
            `Erdos64EG.Tests.k4MersenneCT1Run
          ]
        },
        {
          groupId := "ct1-interface"
          title := "Problem-to-framework encoding"
          role := .frameworkInterface
          explanation :=
            "The Erdős encoding instantiates the reusable edge-rooted CT1 certificate profile without asking the application to manufacture a CT outcome."
          declarations := [
            `Erdos64EG.Internal.mersenneReturnEncoding,
            `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.edgeRootedEncoding
          ]
        }
      ]
      scopeNotes :=
        "This step proves the manuscript's target dictionary and executes both CT1 branches; it does not yet rule out the target-avoiding branch."
      workBound := "One certificate check for C1 and zero checks for the proof-carrying avoiding execution."
    },
    {
      stepId := "erdos.no-proper-core"
      stageId? := some "proof-slice.no-proper-core"
      title := "No proper minimum-degree-three core"
      plainExplanation :=
        "If a proper subgraph still had minimum degree at least three, target avoidance would be inherited and it would be a lexicographically smaller counterexample. Certified CT2 reduction formalizes this contradiction for one arbitrary supplied proper subgraph."
      formalStatement :=
        "H \\subsetneq G \\Longrightarrow \\delta(H) \\le 2"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:no-proper-core", title := "No proper core", nodeIds := [8] }
      ]
      declarationGroups := [
        {
          groupId := "proper-core-semantics"
          title := "Mathematical conclusion"
          role := .semanticTheorem
          explanation :=
            "This theorem is the direct Lean form of the manuscript lemma: every proper finite subgraph of the selected counterexample has minimum degree at most two."
          declarations := [`Erdos64EG.Internal.properSubgraph_minDegree_le_two]
        },
        {
          groupId := "proper-core-execution"
          title := "Certified CT2 execution audit"
          role := .executionAudit
          explanation :=
            "These declarations prove the exact deletion-C2 terminal, typed trace, totality, one-check count, and constant polynomial budget for the supplied proper-subgraph certificate."
          declarations := [
            `Erdos64EG.Internal.properCoreCT2Run_terminal,
            `Erdos64EG.Internal.properCoreCT2Run_trace,
            `Erdos64EG.Internal.properCoreCT2Run_checks,
            `StructuralExhaustion.CT2.runCertifiedReduction,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_total,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_polynomial
          ]
        },
        {
          groupId := "proper-core-provenance"
          title := "Composed prefix and predecessor"
          role := .compositionProvenance
          explanation :=
            "The endpoint constructs the no-proper-core prefix from the original counterexample hypotheses, and the provenance theorem recovers the exact preceding CT1/CT2 output."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedNoProperCorePrefix,
            `Erdos64EG.Internal.noProperCorePrefix_previous
          ]
        },
        {
          groupId := "proper-core-interface"
          title := "Certified-reduction interface"
          role := .frameworkInterface
          explanation :=
            "The packed boundaried graph data supplies the concrete smaller object, while the reusable graph profile owns rank decrease, cycle transport, and the canonical CT2 run."
          declarations := [
            `Erdos64EG.Internal.packedStaticInput,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run
          ]
        }
      ]
      scopeNotes :=
        "The framework checks one proof-specified proper subgraph at a time; the theorem universally quantifies over certificates and does not enumerate subgraphs."
      workBound := "Exactly one local certificate check; degree-zero polynomial budget."
    },
    {
      stepId := "erdos.deletion-criticality"
      stageId? := some "proof-slice.ct2"
      title := "Edge-deletion criticality"
      plainExplanation :=
        "An edge with both endpoints of degree at least four could be deleted while preserving minimum degree three, and deletion cannot create a new cycle. Minimality therefore forces every edge to touch a degree-three vertex."
      formalStatement :=
        "xy \\in E(G) \\Longrightarrow d_G(x)=3 \\lor d_G(y)=3;\\qquad V_{\\ge 4}(G) \\text{ is independent}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:deletion-critical", title := "Deletion criticality", nodeIds := [9, 10, 67] }
      ]
      declarationGroups := [
        {
          groupId := "criticality-semantics"
          title := "Degree-three endpoint consequences"
          role := .semanticTheorem
          explanation :=
            "The first theorem proves the degree-three endpoint alternative for every edge; the second derives independence of the vertices of degree at least four."
          declarations := [
            `Erdos64EG.Internal.deletionCriticality,
            `Erdos64EG.Internal.highDegree_independent
          ]
        },
        {
          groupId := "criticality-route"
          title := "CT1-to-CT2 route execution"
          role := .tacticExecution
          explanation :=
            "The routed profile consumes the actual CT1 avoiding residual, scans the declared dart schedule, and proves local deletion discovery is disabled on the minimal counterexample."
          declarations := [
            `Erdos64EG.Internal.localRoute_disabled,
            `Erdos64EG.Internal.routedProfile,
            `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.edgeRootedDeletionPrefix
          ]
        },
        {
          groupId := "criticality-provenance"
          title := "Verified CT1/CT2 prefix"
          role := .compositionProvenance
          explanation :=
            "These declarations retain the exact CT1 execution, registered-route provenance, disabled CT2 discovery, and both graph-theoretic consequences in one dependent output."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedCT1CT2Prefix,
            `Erdos64EG.Internal.verifiedCT1CT2Prefix,
            `Erdos64EG.Internal.noProperCorePrefix_previous
          ]
        }
      ]
      scopeNotes :=
        "This matches the manuscript deletion argument. The registered route is implementation provenance, not an additional mathematical hypothesis."
      workBound := "At most one scan of the explicit dart list; a closing deletion certificate uses one check."
    },
    {
      stepId := "erdos.boundaried-replacement"
      stageId? := some "proof-slice.ct3"
      title := "Boundaried replacement and uncompressibility"
      plainExplanation :=
        "A proper boundaried atom cannot be replaced by a strictly smaller representative with the same boundary degrees and no worse response in every compatible outside context. Such a replacement would preserve the baseline and target avoidance and contradict minimality."
      formalStatement :=
        "\\operatorname{TargetComplete}(X,X') \\land \\operatorname{rank}(X')<\\operatorname{rank}(X) \\Longrightarrow \\bot"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "def:boundaried-gluing", title := "Boundaried graph and gluing", nodeIds := [11] },
        { label := "lem:degree-profile-fibres", title := "Boundary degree fibres", nodeIds := [11, 36, 37] },
        { label := "lem:context-universality", title := "Context universality", nodeIds := [12, 36] },
        { label := "lem:replacement", title := "Replacement lemma", nodeIds := [13] },
        { label := "cor:uncompressible", title := "Hereditary target-uncompressibility", nodeIds := [14, 38, 39] }
      ]
      declarationGroups := [
        {
          groupId := "replacement-semantics"
          title := "Boundary and replacement theorems"
          role := .semanticTheorem
          explanation :=
            "These declarations separate unequal boundary-degree fibres, prove universal context response, derive global graph obligations from literal gluing, and conclude hereditary target-uncompressibility."
          declarations := [
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.boundaryDegreeProfile_ne_not_targetComplete,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.targetComplete_contextUniversal,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_lexRank_lt,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_preserves_minDegree,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible
          ]
        },
        {
          groupId := "replacement-execution"
          title := "CT3 execution, trace, and budget"
          role := .executionAudit
          explanation :=
            "These theorems pin the canonical compression terminal and trace, prove totality, and bound the certificate-driven execution by a constant polynomial budget."
          declarations := [
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_terminal,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_trace,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_total,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_checks,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_polynomial
          ]
        },
        {
          groupId := "replacement-provenance"
          title := "CT3 prefix and extracted conclusion"
          role := .compositionProvenance
          explanation :=
            "The endpoint extends the exact previous minimal-counterexample prefix; the provenance declarations recover that predecessor and the concrete node-[14] uncompressibility conclusion."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedBoundariedReplacementPrefix,
            `Erdos64EG.Internal.verifiedBoundariedReplacementPrefix,
            `Erdos64EG.Internal.boundariedReplacementPrefix_previous,
            `Erdos64EG.Internal.boundariedReplacementPrefix_uncompressible
          ]
        },
        {
          groupId := "replacement-interface"
          title := "Concrete graph and reusable CT3 interface"
          role := .frameworkInterface
          explanation :=
            "The problem supplies literal packed graph gluing and the power-of-two target; the reusable layer derives exact size, degree, and target transport before executing one certified reduction."
          declarations := [
            `Erdos64EG.Internal.packedStaticInput,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
          ]
        }
      ]
      scopeNotes :=
        "This covers nodes [11]--[14] for normalized decompositions with nonempty boundary. Empty-boundary closed representatives remain a separate manuscript branch. Later invocations at [36]--[39] are not yet formalized."
      workBound := "Proof-level literal gluing and one certified reduction; no universe of contexts, graphs, or replacements is enumerated."
    },
    {
      stepId := "erdos.induced-p13"
      stageId? := some "proof-slice.induced-p13"
      title := "Forced induced P₁₃"
      plainExplanation :=
        "CT1 tests for an induced P₁₃. Its avoiding residual is literal P₁₃-freeness, which the Hegde--Sandeep--Shashank theorem turns into a forbidden power-of-two cycle. Therefore the minimal counterexample contains an induced P₁₃, recorded by a proof-carrying graph embedding."
      formalStatement :=
        "\\delta(G) \\ge 3 \\land \\neg\\operatorname{Target}(G) \\Longrightarrow P_{13} \\hookrightarrow_{\\mathrm{ind}} G"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "thm:p13free", title := "Hegde--Sandeep--Shashank theorem", nodeIds := [15, 16] },
        { label := "cor:p13-exists", title := "Existence of an induced P₁₃", nodeIds := [15, 16] }
      ]
      declarationGroups := [
        {
          groupId := "p13-external"
          title := "Trusted external closure"
          role := .externalTheorem
          explanation :=
            "This isolated axiom is exactly the cited Hegde--Sandeep--Shashank theorem: finite P₁₃-free minimum-degree-three graphs contain a power-of-two cycle. It is the sole trusted external theorem in the repository."
          declarations := [
            `StructuralExhaustion.Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle
          ]
        },
        {
          groupId := "p13-branch-semantics"
          title := "Avoiding-branch contradiction and realization"
          role := .semanticTheorem
          explanation :=
            "These theorems translate P₁₃-freeness into the target via HSS, close it against target avoidance, and derive the induced-path embedding asserted by the manuscript corollary."
          declarations := [
            `Erdos64EG.Internal.hssTarget_of_p13Free,
            `Erdos64EG.Internal.p13FreeBranch_closed,
            `Erdos64EG.Internal.inducedP13_of_hss
          ]
        },
        {
          groupId := "p13-avoiding-execution"
          title := "P₁₃-free CT1 execution"
          role := .executionAudit
          explanation :=
            "These declarations prove the exact avoiding terminal and trace, totality, and zero-check polynomial budget for the proof-carrying P₁₃-free branch."
          declarations := [
            `Erdos64EG.Internal.runP13FreeCT1_terminal,
            `Erdos64EG.Internal.runP13FreeCT1_trace,
            `Erdos64EG.Internal.runP13FreeCT1_total,
            `Erdos64EG.Internal.runP13FreeCT1_polynomial
          ]
        },
        {
          groupId := "p13-positive-execution"
          title := "Induced-path C1 execution"
          role := .executionAudit
          explanation :=
            "These declarations validate the resulting Mathlib induced embedding and prove the exact C1 terminal, trace, totality, and constant work bound."
          declarations := [
            `Erdos64EG.Internal.runInducedP13CT1_terminal,
            `Erdos64EG.Internal.runInducedP13CT1_trace,
            `Erdos64EG.Internal.runInducedP13CT1_total,
            `Erdos64EG.Internal.runInducedP13CT1_polynomial
          ]
        },
        {
          groupId := "p13-provenance"
          title := "Composed induced-path prefix"
          role := .compositionProvenance
          explanation :=
            "The endpoint extends the exact CT3 predecessor on the same selected graph and exposes both that predecessor and the induced-path realization."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedInducedP13Prefix,
            `Erdos64EG.Internal.verifiedInducedP13Prefix,
            `Erdos64EG.Internal.inducedP13Prefix_previous,
            `Erdos64EG.Internal.inducedP13Prefix_realization,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.verifiedInducedPathStage
          ]
        },
        {
          groupId := "p13-interface"
          title := "Induced-path certificate interface"
          role := .frameworkInterface
          explanation :=
            "The application fixes path order thirteen; the reusable graph profile treats a literal Mathlib induced embedding as the CT1 certificate."
          declarations := [
            `Erdos64EG.Internal.inducedP13Profile,
            `StructuralExhaustion.Graph.InducedPath.Profile.encoding
          ]
        }
      ]
      scopeNotes :=
        "The corollary is fully formalized relative to the explicitly isolated HSS theorem. The app must display that trust boundary separately from kernel-proved consequences."
      workBound := "Zero checks on the avoiding proof and one check on a supplied induced embedding; no path or tuple universe is enumerated."
    },
    {
      stepId := "erdos.p13-packing"
      stageId? := some "proof-slice.p13-packing"
      title := "Maximum induced-P₁₃ packing and remainder"
      plainExplanation :=
        "A maximum vertex-disjoint family of induced P₁₃ copies is selected. Maximality makes the complementary induced graph P₁₃-free, and the supports give the exact partition |R| + 13p₁₃ = |V(G)|."
      formalStatement :=
        "|R|+13p_{13}=|V(G)|,\\qquad R \\text{ is } P_{13}\\text{-free}"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "def:p13-packing", title := "Maximum induced-P₁₃ packing", nodeIds := [17] },
        { label := "sec:remainder", title := "P₁₃-free remainder", nodeIds := [25, 26, 27] }
      ]
      declarationGroups := [
        {
          groupId := "packing-semantics"
          title := "Maximum packing and remainder theorems"
          role := .semanticTheorem
          explanation :=
            "These declarations prove maximum cardinality, maximal saturation, the exact partition, hereditary P₁₃-freeness of the remainder, and exclusion of finite internal minimum-degree-three subgraphs."
          declarations := [
            `Erdos64EG.Internal.p13_maximum,
            `Erdos64EG.Internal.p13_saturated,
            `Erdos64EG.Internal.p13Remainder_partition,
            `Erdos64EG.Internal.p13Remainder_free,
            `Erdos64EG.Internal.p13Remainder_componentwise_free,
            `Erdos64EG.Internal.p13Remainder_internalThreeCore_free,
            `Erdos64EG.Internal.p13Remainder_internalSubgraphThreeCore_free
          ]
        },
        {
          groupId := "packing-execution"
          title := "CT12 selected-list audit"
          role := .executionAudit
          explanation :=
            "These theorems prove the exhausted CT12 terminal, iteration bound, exact iteration count p₁₃, and trace-length bound for the selected maximum family."
          declarations := [
            `Erdos64EG.Internal.runP13PackingCT12_terminal,
            `Erdos64EG.Internal.runP13PackingCT12_iterations,
            `Erdos64EG.Internal.runP13PackingCT12_iterations_exact,
            `Erdos64EG.Internal.runP13PackingCT12_trace_bound
          ]
        },
        {
          groupId := "packing-provenance"
          title := "Packing prefix and nonemptiness"
          role := .compositionProvenance
          explanation :=
            "The endpoint extends the exact induced-P₁₃ predecessor; nonemptiness is derived from the retained CT1 embedding rather than supplied by the caller."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedP13PackingPrefix,
            `Erdos64EG.Internal.verifiedP13PackingPrefix,
            `Erdos64EG.Internal.p13PackingPrefix_previous,
            `Erdos64EG.Internal.p13PackingPrefix_routeId,
            `Erdos64EG.Internal.p13PackingPrefix_routedInputExact,
            `Erdos64EG.Internal.p13PackingPrefix_nonempty,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingPrefix,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingRoute_id,
            `StructuralExhaustion.Routes.CT1ToCT12.routeContract
          ]
        },
        {
          groupId := "packing-interface"
          title := "Maximum-disjoint-packing framework"
          role := .frameworkInterface
          explanation :=
            "The Erdős profile fixes induced paths of order thirteen; the reusable core proof-selects a maximum disjoint family and CT12 audits only its selected list."
          declarations := [
            `Erdos64EG.Internal.inducedP13PackingProfile,
            `StructuralExhaustion.CT12.DisjointPacking.Profile.verifiedStage
          ]
        }
      ]
      scopeNotes :=
        "The packing and P₁₃-free remainder clauses are implemented. The later density assertion that R is large is downstream and is not claimed here."
      workBound := "Exactly p₁₃ CT12 iterations, at most |V(G)|; the universe of embeddings and packings is not materialized."
    },
    {
      stepId := "erdos.p13-labels"
      stageId? := some "proof-slice.p13-labels"
      title := "Exact P₁₃ attachment-label algebra"
      plainExplanation :=
        "An outside vertex is labelled by the path positions to which it is adjacent. Target avoidance forbids pairs of positions at gaps two and six. CT10 exhaustively classifies all 8192 bit codes, obtaining exactly 399 legal labels and the manuscript relations Cₛ and Ω₂."
      formalStatement :=
        "\\mathcal L=\\{S\\ne\\varnothing: |i-j|\\notin\\{2,6\\}\\},\\qquad |\\mathcal L|=399"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "lem:labels", title := "Legal label count", nodeIds := [18] },
        { label := "def:p13-curvature-relations", title := "Safety and curvature relations", nodeIds := [18] }
      ]
      declarationGroups := [
        {
          groupId := "label-semantics"
          title := "Legality equivalence and exact table"
          role := .semanticTheorem
          explanation :=
            "These declarations equate the compact bit test and graph-theoretic legality with the manuscript gap condition, certify 399 rows and the exact size distribution, and bound legal label sizes."
          declarations := [
            `Erdos64EG.Internal.p13CodeLegal_iff_gapLegal,
            `Erdos64EG.Internal.p13Legal_iff_gapLegal,
            `Erdos64EG.Internal.p13LegalLabel_count,
            `Erdos64EG.Internal.p13LegalLabel_size_distribution,
            `Erdos64EG.Internal.legalP13Label_card_bounds
          ]
        },
        {
          groupId := "label-budget"
          title := "Finite universe and work ledger"
          role := .workBound
          explanation :=
            "These theorems certify all 8192 candidates, the exact 167792 primitive checks, and the quadratic bound for candidate, direct-case, and row comparisons."
          declarations := [
            `Erdos64EG.Internal.p13Label_candidate_count,
            `Erdos64EG.Internal.p13Label_check_count,
            `Erdos64EG.Internal.p13Label_checks_quadratic
          ]
        },
        {
          groupId := "label-execution"
          title := "Exhaustive CT10 execution"
          role := .executionAudit
          explanation :=
            "These declarations prove the exhaustive terminal, exact typed trace, and totality of the complete attachment-label classification."
          declarations := [
            `Erdos64EG.Internal.runP13LabelCT10_terminal,
            `Erdos64EG.Internal.runP13LabelCT10_trace,
            `Erdos64EG.Internal.runP13LabelCT10_total
          ]
        },
        {
          groupId := "curvature-relations"
          title := "Exact Cₛ and Ω₂ semantics"
          role := .semanticTheorem
          explanation :=
            "These equivalences identify the executable zero/one relations with the manuscript's path-length safety test and two-step curvature condition."
          declarations := [
            `Erdos64EG.Internal.p13C_eq_one_iff,
            `Erdos64EG.Internal.p13OmegaTwo_eq_one_iff
          ]
        },
        {
          groupId := "actual-attachments"
          title := "Transfer to graph attachments"
          role := .semanticTheorem
          explanation :=
            "These theorems prove that every actual nonempty attachment to the retained induced P₁₃ is legal and occurs in the accepted CT10 table."
          declarations := [
            `Erdos64EG.Internal.p13AttachmentLabel_legal,
            `Erdos64EG.Internal.p13AttachmentLabel_accepted
          ]
        },
        {
          groupId := "label-provenance"
          title := "Label-algebra endpoint and predecessor"
          role := .compositionProvenance
          explanation :=
            "The current theorem-bearing endpoint retains the exact CT12 packing predecessor and exposes the verified CT10 stage on the same branch context."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedP13LabelAlgebraPrefix,
            `Erdos64EG.Internal.verifiedP13LabelAlgebraPrefix,
            `Erdos64EG.Internal.p13LabelAlgebraPrefix_previous,
            `Erdos64EG.Internal.p13LabelAlgebraPrefix_stage,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingAttachmentPrefix
          ]
        },
        {
          groupId := "label-interface"
          title := "Compact classification interface"
          role := .frameworkInterface
          explanation :=
            "The application supplies the fixed thirteen-bit legality predicate and its semantic proof; the reusable CT10 profile constructs and verifies the accepted-class table."
          declarations := [
            `Erdos64EG.Internal.p13AttachmentClassification,
            `StructuralExhaustion.CT10.ExhaustiveClassification.Profile.verifiedStage
          ]
        }
      ]
      scopeNotes :=
        "Node [18]'s legal-label table and Cₛ/Ω₂ definitions are implemented. The later triple-count curvature enumeration and constants c_Ω and c₁₃ at node [21] are not yet implemented."
      workBound := "8192 + 399 + 399² = 167792 primitive checks; quadratic in the explicit 8192-code universe."
    },
    {
      stepId := "erdos.surplus-ct6"
      stageId? := some "proof-slice.surplus-ct6"
      title := "Ordered degree-surplus activation"
      plainExplanation :=
        "The reusable CT6 profile tests each declared vertex for a high-centre/non-cubic-neighbour failure. Deletion criticality rules out every failure, so the exact run reaches the active ledger with total Σᵥ(d(v)−3)."
      formalStatement :=
        "|\\mathcal P_{\\rm slot}|=\\sum_v(d(v)-3)=\\sigma(G)"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "lem:sparse-excess-port-extraction", title := "Excess-port extraction", nodeIds := [127] },
        { label := "lem:sparse-port-activation", title := "Cubic-endpoint activation clause", nodeIds := [128] }
      ]
      declarationGroups := [
        {
          groupId := "surplus-execution"
          title := "Ordered CT6 execution and provenance"
          role := .compositionProvenance
          explanation :=
            "The endpoint retains the exact CT10 predecessor and the graph-owned CT6 run on the same selected minimal graph."
          declarations := [
            `StructuralExhaustion.Graph.SurplusPortActivity.run,
            `Erdos64EG.Internal.exists_verifiedSparseSurplusPrefix,
            `Erdos64EG.Internal.verifiedSparseSurplusPrefix,
            `Erdos64EG.Internal.VerifiedSparseSurplusPrefix.previous,
            `Erdos64EG.Internal.runSparseSurplusCT6_terminal,
            `Erdos64EG.Internal.runSparseSurplusCT6_trace
          ]
        },
        {
          groupId := "surplus-semantics"
          title := "Exact surplus and cubic endpoints"
          role := .semanticTheorem
          explanation :=
            "The ledger total and slot cardinality are the degree-surplus sum, and deletion criticality forces every neighbour of a high centre to be cubic."
          declarations := [
            `Erdos64EG.Internal.runSparseSurplusCT6_total_eq_sigma,
            `Erdos64EG.Internal.sparseSurplus_excessPortSlot_card,
            `Erdos64EG.Internal.sparseSurplus_highCenter_neighbor_cubic,
            `Erdos64EG.Internal.runSparseSurplusCT6_checks_linear,
            `Erdos64EG.Internal.runSparseSurplusCT6_primitiveChecks_quadratic,
            `StructuralExhaustion.Graph.SurplusPortActivity.noFailure_of_deletionCritical
          ]
        }
      ]
      scopeNotes :=
        "The CT6 surplus cardinality and cubic-endpoint clauses are implemented. The canonical return/suppression paths Γ(p), the sparse-exit survival routing, and node [129]'s baseline demand remain downstream and are not claimed."
      workBound := "One ordered centre test per vertex and at most |V|² primitive adjacency/degree tests. No paths, subgraphs, graphs, or attachment tables are enumerated."
    },
    {
      stepId := "erdos.surplus-pairs"
      stageId? := some "proof-slice.surplus-pairs"
      title := "Exact surplus-slot pair availability"
      plainExplanation :=
        "CT9 scans only the explicit surplus-slot list. It separates the small state space where at most one slot exists from the branch carrying two distinct slots, which is the exact pair-availability precursor needed before free/blocked response coordinates are defined."
      formalStatement :=
        "\\sigma(G)\\le1\\quad\\text{or}\\quad\\exists p\\ne q\\in\\mathcal P_{\\rm slot}"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "rem:ct9-surplus-slot-stratification", title := "CT9 surplus-slot stratification", nodeIds := [130] },
        { label := "def:sparse-pair-response", title := "Sparse pair-response coordinates", nodeIds := [130] }
      ]
      declarationGroups := [
        {
          groupId := "surplus-pair-route"
          title := "Framework-owned CT6→CT9 transition"
          role := .compositionProvenance
          explanation :=
            "These declarations pin route provenance, exact context preservation, and retention of the CT6 predecessor."
          declarations := [
            `Erdos64EG.Internal.exists_verifiedSurplusPairPrefix,
            `Erdos64EG.Internal.verifiedSurplusPairPrefix,
            `Erdos64EG.Internal.VerifiedSurplusPairPrefix.previous,
            `Erdos64EG.Internal.surplusPairRoute_id,
            `Erdos64EG.Internal.surplusPairRoute_context_preserved,
            `StructuralExhaustion.Routes.CT6ToCT9.routeContract
          ]
        },
        {
          groupId := "surplus-pair-execution"
          title := "Exact CT9 state-space split"
          role := .executionAudit
          explanation :=
            "The routed item count is sigma, the execution is semantically and trace valid, and overload yields two distinct slots."
          declarations := [
            `Erdos64EG.Internal.surplusPair_itemCount_eq_sigma,
            `Erdos64EG.Internal.runSurplusPairCT9_verified,
            `Erdos64EG.Internal.runSurplusPairCT9_traceValid,
            `Erdos64EG.Internal.runSurplusPairCT9_total,
            `Erdos64EG.Internal.surplusPairDecision,
            `Erdos64EG.Internal.surplusPairOfTwoLeSigma_distinct,
            `Erdos64EG.Internal.runSurplusPairCT9_checks_linear
          ]
        }
      ]
      scopeNotes :=
        "This stage proves only pair availability among exact surplus slots. The canonical paths Γ(p), pair-response supports, free/blocked classification, blocker exits, and token accounting remain downstream."
      workBound := "One CT9 partition scan of exactly σ(G) supplied slots; no pairs, paths, subgraphs, graphs, or response tables are enumerated."
    },
    {
      stepId := "erdos.high-center-structure"
      stageId? := some "proof-slice.high-center-structure"
      title := "Four-cycle-free high-neighbourhood structure"
      plainExplanation :=
        "The length-four CT1 avoiding certificate proves that high-centre neighbourhoods are matchings and rules out common external neighbours for nonadjacent ports; deletion criticality supplies cubic endpoints."
      formalStatement :=
        "C_4\\not\\subseteq G\\Longrightarrow G[N(h)]\\text{ is a matching and nonadjacent }x,y\\in N(h)\\text{ have no common neighbour outside }h"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:heavy-neighbourhood-normal-form", title := "High-neighbourhood normal form", nodeIds := [64, 65] }
      ]
      declarationGroups := [{
        groupId := "high-center-ct1"
        title := "Exact CT1 certificate and graph consequences"
        role := .semanticTheorem
        explanation := "The graph layer owns the literal four-cycle construction and both structural consequences."
        declarations := [
          `StructuralExhaustion.Graph.HighCenterStructure.verifiedStage,
          `Erdos64EG.Internal.exists_verifiedHighCenterStructurePrefix,
          `Erdos64EG.Internal.verifiedHighCenterStructurePrefix,
          `Erdos64EG.Internal.VerifiedHighCenterStructurePrefix.previous,
          `Erdos64EG.Internal.runFourCycleAvoidingCT1_terminal,
          `Erdos64EG.Internal.runFourCycleAvoidingCT1_trace,
          `Erdos64EG.Internal.runFourCycleAvoidingCT1_total,
          `Erdos64EG.Internal.highCenter_neighborhood_matching,
          `Erdos64EG.Internal.highCenter_nonadjacent_noCommonOutside
        ]
      }]
      scopeNotes := "This proves the local normal form, not the later fan-completion routing."
      workBound := "Proof-carrying CT1 avoiding run with zero realization checks."
    },
    {
      stepId := "erdos.port-classification"
      stageId? := some "proof-slice.port-classification"
      title := "Canonical selected-port types"
      plainExplanation :=
        "Each canonical degree-surplus slot selects an actual incident endpoint; deletion criticality produces its two shoulders, and CT10 classifies the shoulder chord as open or triangular."
      formalStatement :=
        "p\\in\\mathcal P_{\\rm exc}\\Longrightarrow |s(p)|=2\\ \\text{ and }\\ p\\text{ is open or triangular}"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:surplus-ports", title := "Surplus ports and excess selectors", nodeIds := [64] },
        { label := "def:heavy-center-triangular-port", title := "High centers and port types", nodeIds := [65] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [64, 65] }
      ]
      declarationGroups := [{
        groupId := "selected-port-ct10"
        title := "Graph-owned exact CT10 table"
        role := .executionAudit
        explanation := "The table contains only the explicit surplus-slot list and the two port types."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPortActivity.verifiedClassificationStage,
          `Erdos64EG.Internal.exists_verifiedSurplusPortClassificationPrefix,
          `Erdos64EG.Internal.surplusPortClassification_stateSpace,
          `Erdos64EG.Internal.runSurplusPortClassificationCT10_checks_quadratic,
          `StructuralExhaustion.Graph.SurplusPortActivity.shoulderVertices_length
        ]
      }]
      scopeNotes := "This classifies selected ports; it does not prove the heavy-centre triangular lower bound over all incident ports."
      workBound := "At most 2|V|²+2 primitive checks; no graph or subset enumeration."
    },
    {
      stepId := "erdos.open-port-pairs"
      stageId? := some "proof-slice.open-port-pairs"
      title := "Open selected ports by centre"
      plainExplanation :=
        "CT9 partitions the open selected-slot subtype by its actual centre and retains both state-space branches."
      formalStatement :=
        "(\\forall h,|\\mathcal P_{\\rm open}(h)|\\le1)\\ \\lor\\ (\\exists p\\ne q,\\ c(p)=c(q))"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "lem:same-center-open-port-compatibility", title := "Same-center open ports", nodeIds := [66] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [66] }
      ]
      declarationGroups := [{
        groupId := "open-port-ct9"
        title := "Capacity-one centre fibres"
        role := .executionAudit
        explanation := "Overload extracts one pair from the first overloaded fibre; the runner never constructs the pair universe."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPortActivity.verifiedOpenPairStage,
          `Erdos64EG.Internal.exists_verifiedOpenPortPairPrefix,
          `Erdos64EG.Internal.openPortPairDecision,
          `Erdos64EG.Internal.runOpenPortPairCT9_checks_cubic,
          `StructuralExhaustion.Graph.SurplusPortActivity.openPairDecision
        ]
      }]
      scopeNotes := "The same-centre pair is not yet asserted fan-compatible; endpoint and shoulder disjointness remain downstream."
      workBound := "At most |V|³+|V| primitive fibre checks; pairs are not enumerated."
    },
    {
      stepId := "erdos.open-port-responses"
      stageId? := some "proof-slice.open-port-responses"
      title := "Overload-only endpoint response comparison"
      plainExplanation :=
        "The registered CT9-to-CT7 route is taken only on an actual overload residual. It compares the two canonical endpoints over the declared vertex contexts and otherwise leaves the bounded CT9 branch untouched."
      formalStatement :=
        "\\text{bounded centre fibres}\\ \\lor\\ (\\exists p,q,\\ R_{x(p)}\\ne R_{x(q)}\\ \\lor\\ R_{x(p)}=R_{x(q)})"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [66, 130] },
        { label := "def:sparse-pair-response", title := "Sparse pair-response coordinates", nodeIds := [130] }
      ]
      declarationGroups := [{
        groupId := "open-response-route"
        title := "Framework-owned CT9→CT7 route"
        role := .compositionProvenance
        explanation := "The route preserves context and maps the exact source pair to the two target objects."
        declarations := [
          `Erdos64EG.Internal.exists_verifiedOpenPortResponsePrefix,
          `Erdos64EG.Internal.openPortResponse_stateSpace,
          `StructuralExhaustion.Routes.CT9ToCT7.routeContract,
          `StructuralExhaustion.Graph.OpenPortResponse.route_id,
          `StructuralExhaustion.Graph.AdjacencyResponse.checks_linear
        ]
      }]
      scopeNotes := "These are raw vertex-adjacency responses, not the manuscript's full connected-support target-response coordinates."
      workBound := "Two linear scans, at most 2|V|+1 checks, only on the overload branch."
    },
    {
      stepId := "erdos.shoulder-ledger"
      stageId? := some "proof-slice.shoulder-ledger"
      title := "Exact selected-port shoulder ledger"
      plainExplanation :=
        "CT5 checks one local shoulder-pair witness per selected slot and reaches the exact charge terminal with total twice the slot count."
      formalStatement :=
        "\\sum_{p\\in\\mathcal P_{\\rm exc}}|s(p)|=2|\\mathcal P_{\\rm exc}|"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:surplus-ports", title := "Surplus ports and shoulder pairs", nodeIds := [64] },
        { label := "def:triangular-fan-core", title := "Triangular fan shoulders", nodeIds := [68] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [64, 68] }
      ]
      declarationGroups := [{
        groupId := "shoulder-ct5"
        title := "Exact CT5 charge ledger"
        role := .executionAudit
        explanation := "The graph profile proves the witness support, exact ledger arithmetic, terminal, trace, totality, and quadratic bound."
        declarations := [
          `StructuralExhaustion.Graph.PortShoulderLedger.verifiedStage,
          `Erdos64EG.Internal.exists_verifiedPortShoulderLedgerPrefix,
          `Erdos64EG.Internal.runPortShoulderLedgerCT5_terminal,
          `Erdos64EG.Internal.runPortShoulderLedgerCT5_total,
          `Erdos64EG.Internal.runPortShoulderLedgerCT5_checks_quadratic,
          `StructuralExhaustion.Graph.PortShoulderLedger.run_trace_charge
        ]
      }]
      scopeNotes := "The ledger certifies the two shoulders only; it does not classify their completion incidences."
      workBound := "One singleton witness and one contribution per slot, bounded by 2|V|²+2."
    },
    {
      stepId := "erdos.open-port-compatibility"
      stageId? := some "proof-slice.open-port-compatibility"
      title := "Exact same-centre fan compatibility"
      plainExplanation :=
        "For the exact pair returned by a CT9 centre-fibre overload, the framework proves that nonadjacent canonical endpoints have disjoint shoulder pairs and cannot occur as one another's shoulders. Endpoint adjacency is retained as the complementary branch."
      formalStatement :=
        "p\\ne q\\land c(p)=c(q)\\Longrightarrow x(p)x(q)\\in E(G)\\ \\lor\\ \\{p,q\\}\\text{ is fan-compatible}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:fan-compatible-open-ports", title := "Fan-compatible open ports", nodeIds := [69] },
        { label := "lem:same-center-open-port-compatibility", title := "Same-center open ports", nodeIds := [69] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69, 130] }
      ]
      declarationGroups := [{
        groupId := "open-port-compatibility-ct7"
        title := "Framework-owned CT7 interpretation"
        role := .semanticTheorem
        explanation := "The graph theorem uses the exact routed overload pair and the already verified four-cycle exclusion; it does not enumerate pairs or contexts."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPortActivity.portEndpoint_injective_of_sameCenter,
          `StructuralExhaustion.Graph.OpenPortCompatibility.fanCompatible_of_nonadjacent,
          `StructuralExhaustion.Graph.OpenPortCompatibility.stateSpace,
          `Erdos64EG.Internal.openPortCompatibility_stateSpace,
          `Erdos64EG.Internal.exists_verifiedOpenPortCompatibilityPrefix
        ]
      }]
      scopeNotes := "This closes the manuscript's conditional same-centre compatibility lemma. It does not eliminate the adjacent-endpoint branch or prove the later heavy-centre triangular count and shoulder-completion routing."
      workBound := "The semantic proof is noncomputational after the prior CT9/CT7 outputs; CT7 has already used at most 2|V|+1 checks."
    },
    {
      stepId := "erdos.high-center-port-dichotomy"
      stageId? := some "proof-slice.high-center-port-dichotomy"
      title := "All-incident-port heavy-centre dichotomy"
      plainExplanation :=
        "CT10 classifies the exact neighbour schedule of each high centre. If no compatible open pair exists, all open endpoints are pairwise adjacent; the four-cycle-free matching neighbourhood permits at most two, so every remaining port is triangular."
      formalStatement :=
        "h:\\ d(h)\\ge4\\Longrightarrow (\\exists\\text{ compatible open }p,q)\\ \\lor\\ |\\mathcal P_{\\rm tri}(h)|\\ge d(h)-2"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:heavy-center-triangular-alternative", title := "Heavy-center triangular alternative", nodeIds := [69] },
        { label := "cor:heavy-center-local-dichotomy", title := "Heavy-center local dichotomy", nodeIds := [69] },
        { label := "cor:degree-four-local-activation", title := "Degree-four local activation", nodeIds := [69] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69] }
      ]
      declarationGroups := [{
        groupId := "all-port-ct10"
        title := "Framework-owned all-port CT10 profile"
        role := .semanticTheorem
        explanation := "The datum list is one centre's declared neighbour schedule. Generic graph lemmas own the classification, cardinality partition, matching argument, execution certificate, and linear bound."
        declarations := [
          `StructuralExhaustion.Graph.HighCenterPort.localDichotomy,
          `StructuralExhaustion.Graph.HighCenterPort.verifiedStage,
          `StructuralExhaustion.Graph.HighCenterPort.classificationChecks_linear,
          `Erdos64EG.Internal.highCenterPort_stage,
          `Erdos64EG.Internal.exists_verifiedHighCenterPortDichotomyPrefix
        ]
      }]
      scopeNotes := "This exactly proves the numerical local dichotomy, including the heavy-centre and degree-four counts. The downstream Type B routing clauses in the degree-four corollary and all shoulder-completion claims remain unimplemented."
      workBound := "At most 2d(h)+2 primitive CT10 row checks for a requested centre, bounded by 2|V|+2; no port-pair universe is constructed."
    },
    {
      stepId := "erdos.triangular-shoulder-completion"
      stageId? := some "proof-slice.triangular-shoulder-completion"
      title := "Triangular shoulder-completion bookkeeping"
      plainExplanation :=
        "CT5 visits the two shoulders of each actual triangular port. Minimum degree supplies a completion edge, deletion criticality makes a central shoulder cubic, and literal four-cycle exclusions prove both central uniqueness and the ban on other centre-neighbour endpoints."
      formalStatement :=
        "p\\text{ triangular},\\ s\\in S(p)\\Longrightarrow \\exists sy\\text{ completing }s,\\text{ with the central and }N(h)\\setminus\\{h\\}\\text{ exclusions}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:triangular-fan-core", title := "Triangular fan core and shoulder completions", nodeIds := [68, 78] },
        { label := "lem:triangular-shoulder-completion", title := "Shoulder-completion bookkeeping", nodeIds := [78] }
      ]
      declarationGroups := [{
        groupId := "triangular-shoulder-ct5"
        title := "Framework-owned CT5 completion ledger"
        role := .semanticTheorem
        explanation := "Sites are triangular-port shoulders and witnesses are declared vertices. The framework owns the search, exact charge trace, local graph clauses, totality, and quadratic bound."
        declarations := [
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.exists_completion,
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.not_both_shoulders_central,
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.completion_eq_center_of_central,
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.completion_not_other_center_neighbor,
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.checks_quadratic,
          `StructuralExhaustion.Graph.TriangularShoulderCompletion.verifiedStage,
          `Erdos64EG.Internal.triangularShoulder_stage,
          `Erdos64EG.Internal.exists_verifiedTriangularShoulderCompletionPrefix
        ]
      }]
      scopeNotes := "This proves all four clauses of the shoulder-completion lemma. The later CT1 return stage constructs Q; the full completion-endpoint classification remains downstream."
      workBound := "At most 2|V|²+2|V|+2 primitive checks per requested centre; the site family has at most 2|V| shoulders and no paths, subsets, or port pairs are enumerated."
    },
    {
      stepId := "erdos.bridgeless"
      stageId? := some "proof-slice.bridge-contraction"
      title := "Bridgelessness by exact contraction"
      plainExplanation :=
        "For a hypothetical bridge uv, the framework removes v, reattaches its non-bridge incidences to u, proves that no degree is lost, and lifts every contracted simple cycle with the same length. The smaller target-avoiding graph contradicts packed minimality through CT2."
      formalStatement :=
        "e\\in E(G)\\Longrightarrow e\\text{ is not a bridge}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:bridgeless", title := "Bridgelessness of the minimal counterexample" }
      ]
      declarationGroups := [{
        groupId := "bridge-contraction-ct2"
        title := "Framework-owned bridge reduction"
        role := .semanticTheorem
        explanation := "The graph layer owns the literal contraction, degree injection, side-consistent cycle lift, rank decrease, target transport, and constant-work certified-reduction execution."
        declarations := [
          `StructuralExhaustion.Graph.BridgeContraction.preserves_minDegree,
          `StructuralExhaustion.Graph.BridgeContraction.hasCycleWithLength_of_contraction,
          `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeReductionStage,
          `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeCT2Run_total,
          `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.bridgeCT2Run_checks,
          `Erdos64EG.Internal.bridgeReductionStage,
          `Erdos64EG.Internal.dart_not_bridge,
          `Erdos64EG.Internal.exists_verifiedBridgeReductionPrefix
        ]
      }]
      scopeNotes := "This proves that every dart is non-bridging. The following framework transition consumes that result to construct the triangular-port return."
      workBound := "One certified CT2 check on a hypothetical bridge; no graph, component, path, cycle, subset, or replacement universe is enumerated."
    },
    {
      stepId := "erdos.triangular-port-return"
      stageId? := some "proof-slice.triangular-port-return"
      title := "Triangular-port returns enter through shoulders"
      plainExplanation :=
        "For every triangular port, the framework selects one simple return supplied by non-bridging, proves that its first vertex is a shoulder, removes the port endpoint, reconstructs a simple cycle of length |Q|+2, and exposes the exact four initial landing alternatives."
      formalStatement :=
        "p=(h,x)\\text{ triangular}\\Longrightarrow\\exists s\\in S(p),\\ Q\\subseteq G-x,\\ |C(Q)|=|Q|+2"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:triangular-port-return", title := "Port returns enter through shoulders", nodeIds := [79] }
      ]
      declarationGroups := [{
        groupId := "triangular-return-ct1"
        title := "Framework-owned CT2-to-CT1 return stage"
        role := .semanticTheorem
        explanation := "The bridge stage supplies a non-bridge theorem, Mathlib supplies one simple reachable path, and CT1 validates the resulting proof-carrying return certificate."
        declarations := [
          `StructuralExhaustion.Graph.DartReturn.ofNotBridge,
          `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.BridgeReductionStage.dartReturn,
          `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.endpoint_not_mem_path,
          `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.cycle_isCycle,
          `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.cycle_length,
          `StructuralExhaustion.Graph.TriangularPortReturn.Certificate.landingAlternative,
          `StructuralExhaustion.Graph.TriangularPortReturn.verifiedStage,
          `Erdos64EG.Internal.triangularPortRoot,
          `Erdos64EG.Internal.triangularPortReturn_length_ne,
          `Erdos64EG.Internal.triangularPortReturnStage,
          `Erdos64EG.Internal.exists_verifiedTriangularPortReturnPrefix
        ]
      }]
      scopeNotes := "The initial split includes the two-edge shoulder-then-central case omitted by the former manuscript sentence. The next stage classifies noncentral completion endpoints as cross-triangular or outside."
      workBound := "Exactly one CT1 certificate check; the path witness is selected from a proved existential and no walk, path, cycle, subset, subgraph, or graph family is enumerated."
    },
    {
      stepId := "erdos.triangular-first-landing"
      stageId? := some "proof-slice.triangular-first-landing"
      title := "First landing exhaustion for triangular shoulders"
      plainExplanation :=
        "Every actual shoulder-completion incidence is classified by CT10. Four-cycle freeness rules out every noncentral neighbour of the fan centre; completion-edge exclusions rule out its own port data; the remaining fan-core endpoint is exactly a shoulder of another triangular port, and every other endpoint is outside. The framework also applies this classification to the first noncentral completion on the verified return path."
      formalStatement :=
        "sy\\text{ a shoulder completion}\\Longrightarrow y=h\\ \\lor\\ y\\in\\bigcup_{j\\ne i}S_j\\ \\lor\\ y\\notin V(F_h(\\mathcal T_h))\\cup N(h)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:triangular-first-landing", title := "First landing exhaustion for triangular shoulders", nodeIds := [80] }
      ]
      declarationGroups := [{
        groupId := "triangular-first-landing-ct10"
        title := "Framework-owned finite landing classification"
        role := .semanticTheorem
        explanation := "The graph layer owns the literal completion-incidence universe, the three semantic classes, the CT10 runner, trace and totality audits, the quadratic budget, and ordinary composition with the preceding CT1 return."
        declarations := [
          `StructuralExhaustion.Graph.TriangularFirstLanding.landing_exhaustive,
          `StructuralExhaustion.Graph.TriangularFirstLanding.classOf_sound,
          `StructuralExhaustion.Graph.TriangularFirstLanding.run_traceValid,
          `StructuralExhaustion.Graph.TriangularFirstLanding.run_total,
          `StructuralExhaustion.Graph.TriangularFirstLanding.checks_quadratic,
          `StructuralExhaustion.Graph.TriangularFirstLanding.verifiedStage,
          `StructuralExhaustion.Graph.TriangularFirstLanding.classifyReturn,
          `Erdos64EG.Internal.triangularFirstLandingStage,
          `Erdos64EG.Internal.triangularPortReturn_classified,
          `Erdos64EG.Internal.exists_verifiedTriangularFirstLandingPrefix
        ]
      }]
      scopeNotes := "This proves node [80] for every actual completion incidence and for the verified return's first noncentral completion. Cross-shoulder multiplicity at node [81] is the next stage."
      workBound := "At most 6n²+3 CT10 classification and row checks on the explicit shoulder-site × declared-vertex table; no path, subgraph, graph, or context universe is enumerated."
    },
    {
      stepId := "erdos.triangular-cross-shoulder"
      stageId? := some "proof-slice.triangular-cross-shoulder"
      title := "Cross-shoulder multiplicity"
      plainExplanation :=
        "For two distinct triangular ports, CT9 scans their four possible shoulder pairs as one capacity-one fibre. Distinct port endpoints are nonadjacent and the shoulder pairs are disjoint. Two cross edges sharing a shoulder force four distinct neighbours there; two disjoint cross edges form a four-cycle. Since four-cycles are excluded, either a high shoulder is routed to the surplus branch or at most one cross edge survives."
      formalStatement :=
        "|E(S_i,S_j)|\\ge2\\Longrightarrow (\\exists s\\in S_i\\cup S_j,\\ d_G(s)\\ge4)\\ \\lor\\ C_4\\subseteq G"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:triangular-cross-shoulder", title := "Cross-shoulder multiplicity", nodeIds := [81] }
      ]
      declarationGroups := [{
        groupId := "triangular-cross-shoulder-ct9"
        title := "Framework-owned capacity-one cross-edge fibre"
        role := .semanticTheorem
        explanation := "The graph layer owns the four-candidate universe, port and shoulder disjointness, the CT9 run, overload interpretation, cubic bounded run, trace audit, and constant work bound."
        declarations := [
          `StructuralExhaustion.Graph.TriangularCrossShoulder.endpoint_nonadjacent,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.shoulder_pairs_disjoint,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.highShoulder_of_two,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.stateSpace,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.boundedRunOfCubic,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.checks_constant,
          `StructuralExhaustion.Graph.TriangularCrossShoulder.verifiedStage,
          `Erdos64EG.Internal.triangularCrossShoulderStage,
          `Erdos64EG.Internal.triangularCrossShoulder_stateSpace,
          `Erdos64EG.Internal.exists_verifiedTriangularCrossShoulderPrefix
        ]
      }]
      scopeNotes := "This proves node [81] with the high-shoulder branch kept explicit. It does not assume every shoulder is cubic; that hypothesis merely forces the supplied bounded CT9 constructor."
      workBound := "At most five primitive CT9 partition checks on four explicit shoulder pairs and one unit label; no pair set, path, subgraph, or graph universe is enumerated."
    },
    {
      stepId := "erdos.fan-closed-port"
      stageId? := some "proof-slice.fan-closed-port"
      title := "Fan-compatible pairs give fan-closed local data"
      plainExplanation :=
        "The P13 packing defines the window side and its literal complement. For two distinct fan-compatible open ports whose four oriented non-centre incidences are assigned to the Type-B envelope, CT5 checks those four sites. Both endpoint remainder facts and all assignment facts are consumed to derive two fan-closed ports; endpoint injectivity and the two-shoulder normal form prove that the four carriers are distinct."
      formalStatement :=
        "FanCompatible(p,q) ∧ x_p,x_q ∈ R ∧ Assigned(xa_p,xb_p,ya_q,yb_q) → FanClosed(p) ∧ FanClosed(q)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-window-incidence-profile", title := "Type B window-incidence profile", nodeIds := [72] },
        { label := "def:fan-closed-port", title := "Fan-closed surplus port", nodeIds := [72] },
        { label := "lem:compatible-pair-fan-closure", title := "Fan-compatible open pairs give fan-closed local data", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "fan-closed-port-ct5"
        title := "Framework-owned four-incidence ledger"
        role := .semanticTheorem
        explanation := "The graph layer computes window/non-window incidence kinds and support types, executes CT5 on Bool×Bool with one Unit witness per site, and derives closure, distinctness, trace validity, totality, and the exact check count."
        declarations := [
          `StructuralExhaustion.Graph.FanClosedPort.incidenceKind_exact,
          `StructuralExhaustion.Graph.FanClosedPort.first_fanClosed,
          `StructuralExhaustion.Graph.FanClosedPort.second_fanClosed,
          `StructuralExhaustion.Graph.FanClosedPort.carriers_nodup,
          `StructuralExhaustion.Graph.FanClosedPort.verifiedStage,
          `Erdos64EG.Internal.p13FanWindowProfile,
          `Erdos64EG.Internal.fanClosedPairStage,
          `Erdos64EG.Internal.exists_verifiedFanClosedPortPrefix
        ]
      }]
      scopeNotes := "This proves the local fan-closure block at node [72]. The logically later claim that a failed global disjoint choice yields a minimal Type-B overlap obstruction remains with lem:typeB-bridge-to-overlap, after its prerequisites."
      workBound := "Exactly ten primitive checks: four singleton witness tests, four contributions, and two comparisons; no vertex, pair, path, subgraph, graph, or assignment universe is enumerated."
    },
    {
      stepId := "erdos.fan-closed-mass"
      stageId? := some "proof-slice.fan-closed-mass"
      title := "Compatible-pair cubic-closed mass and deficit"
      plainExplanation :=
        "The prior CT5 charge residual is routed to CT14 without changing the selected graph or branch state. CT14's members are precisely the actual vertices adjacent to the centre that are cubic, lie in the P13-packing remainder, and have every non-centre incidence assigned. Each fan-closed port endpoint satisfies this predicate. Endpoint injectivity embeds Bool into the member subtype, so its cardinality and Unit-label multiplicity are at least two; for centre degree k at least four, the quarter-deficit numerator 4c+k-11 is at least k-3 and is positive."
      formalStatement :=
        "FanCompatible(p,q) ∧ FanClosed(p) ∧ FanClosed(q) → 2 ≤ c and 0 < 4c+k-11"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "prop:fan-closed-port-typeB-routing", title := "Fan-closed ports route to the Type B fan ledger", nodeIds := [72] },
        { label := "cor:compatible-pair-typeB-routing", title := "Fan-compatible open pairs route to the Type B fan ledger", nodeIds := [69, 72] }
      ]
      declarationGroups := [{
        groupId := "fan-closed-mass-ct14"
        title := "Framework-owned CT5-to-CT14 mass route"
        role := .semanticTheorem
        explanation := "The route owns source-residual extraction, context preservation, trigger construction, and provenance. The graph layer owns the semantic member subtype, exact CT14 mass/multiplicity ledger, injection proof, deficit arithmetic, trace, totality, and polynomial audit."
        declarations := [
          `StructuralExhaustion.Routes.CT5ToCT14.routeContract,
          `StructuralExhaustion.Routes.CT5ToCT14.buildInput,
          `StructuralExhaustion.Routes.CT5ToCT14.generated_route_id,
          `StructuralExhaustion.Graph.FanClosedPortMass.fanClosed_is_cubicClosed,
          `StructuralExhaustion.Graph.FanClosedPortMass.two_le_cubicClosed_card,
          `StructuralExhaustion.Graph.FanClosedPortMass.multiplicity_eq_card,
          `StructuralExhaustion.Graph.FanClosedPortMass.deficitNumerator_positive,
          `StructuralExhaustion.Graph.FanClosedPortMass.verifiedStage,
          `Erdos64EG.Internal.fanClosedMassStage,
          `Erdos64EG.Internal.exists_verifiedFanClosedMassPrefix
        ]
      }]
      scopeNotes := "This verifies the actual cubic-closed count and positive-deficit arithmetic in the local routing proposition. The hybrid B1 half-credit capacity and the later global B2 disjointness/overlap alternatives are not claimed by this stage."
      workBound := "At most 4n²+4n+1 primitive predicate/member checks. The executable subtype list has at most n members and is scanned a constant number of times; no subsets, assignments, paths, subgraphs, or graphs are enumerated."
    },
    {
      stepId := "erdos.hybrid-fan-incidence"
      stageId? := some "proof-slice.hybrid-fan-incidence"
      title := "Hybrid window/non-window incidence budget"
      plainExplanation :=
        "The actual cubic-closed subtype from the preceding CT14 result is refined to exactly two non-centre incidences per member. Four-cycle avoidance makes their non-centre endpoints pairwise distinct. A second CT14 ledger labels every incidence as window or non-window, records exact multiplicities, and gives every incidence two quarter-units. Under the marked-fan bound k≤8, the total 4c quarter-units exceed the deficit 4c+k-11 by at least three; after applying all window credit, the non-window credit pays the remaining demand."
      formalStatement :=
        "k≤8 ⇒ 3≤4c-(4c+k-11),\\quad I_W+I_R=2c"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:typeB-hybrid-incidence", title := "Hybrid incidence ledger", nodeIds := [72] },
        { label := "lem:typeB-hybrid-incidence-budget", title := "Hybrid incidence budget", nodeIds := [72] },
        { label := "lem:typeB-hybrid-B1", title := "Local hybrid B1 entry", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "hybrid-fan-incidence-ct14"
        title := "Framework-owned CT14-to-CT14 incidence refinement"
        role := .semanticTheorem
        explanation := "The route owns capacity-residual extraction, context preservation, trigger construction, and provenance. The graph layer constructs the literal two-per-member incidence universe, proves graph-theoretic endpoint disjointness, runs CT14, proves exact binary-label multiplicities and deficit arithmetic, and records totality and polynomial work."
        declarations := [
          `StructuralExhaustion.Routes.CT14ToCT14.routeContract,
          `StructuralExhaustion.Routes.CT14ToCT14.buildInput,
          `StructuralExhaustion.Routes.CT14ToCT14.generated_route_id,
          `StructuralExhaustion.Graph.HybridFanIncidence.other_injective,
          `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card,
          `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card_le_twice_vertices,
          `StructuralExhaustion.Graph.HybridFanIncidence.multiplicity_partition,
          `StructuralExhaustion.Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack,
          `StructuralExhaustion.Graph.HybridFanIncidence.nonWindow_credit_pays_remaining,
          `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
          `Erdos64EG.Internal.hybridFanIncidenceStage,
          `Erdos64EG.Internal.exists_verifiedHybridFanIncidencePrefix
        ]
      }]
      scopeNotes := "This verifies the local incidence universe, carrier disjointness, exact hybrid multiplicities, and half-credit arithmetic. It deliberately takes k≤8 as the marked-fan branch input. The later identification of this local entry with the manuscript's global B1 alternative and the B2 overlap/blocker closure are not claimed."
      workBound := "At most 4n²+20n+1 primitive checks. The only stored refinement universe has exactly 2c≤2n incidences; no closed-neighbour×vertex table, subsets, assignments, paths, subgraphs, or graphs are enumerated."
    },
    {
      stepId := "erdos.direct-fan-window"
      stageId? := some "proof-slice.direct-fan-window"
      title := "Direct fan-window cycle eliminations"
      plainExplanation :=
        "For two distinct external neighbours closed on the same induced path window, the framework expands the exact direct-cycle-free clauses. An internal forbidden gap closes through one external vertex; a forbidden cross-distance closes through the two-edge fan path; interlacing endpoints close through two disjoint induced-path segments. Each branch is a literal Mathlib simple cycle. On the target-avoiding selected graph, the certificate-driven CT1 avoiding run proves that no such violation exists."
      formalStatement :=
        "h\\notin V(P) \\land \\neg\\operatorname{DirectFree}(u,v) \\Longrightarrow \\exists C,\\ |C|\\in\\{4,8,16\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:closed-fan-window-pair", title := "Closed fan-window pair", nodeIds := [72] },
        { label := "def:direct-cycle-free-closed-pair", title := "Direct-cycle-free closed pair", nodeIds := [72] },
        { label := "lem:typeB-direct-fan-window-cycles", title := "Direct fan-window cycle eliminations", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "direct-fan-window-ct1"
        title := "Framework-owned direct-cycle CT1 profile"
        role := .semanticTheorem
        explanation := "The graph layer owns ordered segment support bounds, one-segment connector cycles, two-segment interlacing cycles, the exact finite violation type, its arithmetic equivalence, cycle construction, CT1 execution, trace, totality, and the zero-check avoiding result. The Erdős layer supplies only the power-of-two predicate and selected target-avoiding context."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathAttachment.mem_ambientSegment_support_bounds,
          `StructuralExhaustion.Graph.InducedPathBridge.connectorCycle,
          `StructuralExhaustion.Graph.InducedPathBridge.interlacingCycle,
          `StructuralExhaustion.Graph.FanWindowCycle.directCycleFree_iff,
          `StructuralExhaustion.Graph.FanWindowCycle.cycleOfViolation,
          `StructuralExhaustion.Graph.FanWindowCycle.verifiedAvoidingStage,
          `Erdos64EG.Internal.directFanWindowStage,
          `Erdos64EG.Internal.sameWindowPair_directCycleFree,
          `Erdos64EG.Internal.exists_verifiedDirectFanWindowPrefix
        ]
      }]
      scopeNotes := "This is the complete same-window direct-cycle lemma. The formal statement makes the necessary condition h∉V(P) explicit; the manuscript now records that ordinary remainder-side fan centers satisfy it and that packed-window handoff centers use the grouped-envelope branch. The distinct two-window lemma and global B1/B2 bridge remain downstream."
      workBound := "The CT1 avoiding execution performs zero realization checks. A positive branch validates one already constructed cycle in one check. All path segments are symbolic Mathlib walks; no labels, walks, paths, vertex tuples, subsets, subgraphs, or graphs are enumerated."
    },
    {
      stepId := "erdos.two-window-cycle"
      stageId? := some "proof-slice.two-window-cycle"
      title := "Two-window direct cycle eliminations"
      plainExplanation :=
        "For two external vertices incident with two vertex-disjoint induced windows, the graph layer constructs an orientation-independent bridge through each window. The bridge tails are disjoint because window supports are disjoint and both external vertices lie outside them. Their concatenation is therefore a literal simple cycle of exact length 4+|i-j|+|a-b|. The selected target-avoiding context excludes every accepted total through a zero-check CT1 run."
      formalStatement :=
        "|i-j|+|a-b|\\in\\{0,4,12\\} \\Longrightarrow \\exists C,\\ |C|\\in\\{4,8,16\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-two-window-cycles", title := "Two-window direct cycle eliminations", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "two-window-cycle-ct1"
        title := "Framework-owned two-window CT1 profile"
        role := .semanticTheorem
        explanation := "The graph layer owns the orientation-independent bridge, its exact length and tail-support classification, the two-window data contract, the literal simple-cycle constructor, target-avoidance theorem, CT1 trace, totality, and zero-check audit. The Erdős layer only retains the selected power-of-two avoiding context."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathBridge.unorderedBridge,
          `StructuralExhaustion.Graph.InducedPathBridge.unorderedBridge_tail_member,
          `StructuralExhaustion.Graph.TwoWindowCycle.cycle,
          `StructuralExhaustion.Graph.TwoWindowCycle.directCycleFree_of_avoids,
          `StructuralExhaustion.Graph.TwoWindowCycle.verifiedAvoidingStage,
          `Erdos64EG.Internal.twoWindowCycleStage,
          `Erdos64EG.Internal.packedTwoWindow_directCycleFree,
          `Erdos64EG.Internal.exists_verifiedTwoWindowCyclePrefix
        ]
      }]
      scopeNotes := "This is the complete distinct-two-window direct-cycle lemma. The positive-deficit arithmetic and global B1/B2 carrier bridge remain downstream."
      workBound := "The CT1 avoiding execution performs zero realization checks; a positive branch validates one constructed cycle in one check. No position pairs, labels, walks, paths, vertex tuples, subsets, subgraphs, or graphs are enumerated."
    },
    {
      stepId := "erdos.fan-label-packing"
      stageId? := some "proof-slice.fan-label-packing"
      title := "Certificate-marked fan degree cap"
      plainExplanation :=
        "The marked-fan contract supplies a legal nonempty P13 label for each actual incident port and pairwise C2 compatibility. The graph layer chooses the least position in each label. A cached eight-slot cover puts only equal or distance-four positions in one slot, so compatibility makes the slot map injective. CT9 scans those eight fibres and proves the fan has at most eight neighbours."
      formalStatement :=
        "(\\forall u\\ne v,\\ C_2(S_h(u),S_h(v))=1) \\Longrightarrow d_G(h)\\le8"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:marked-typeB-fan", title := "Marked Type B fan", nodeIds := [70] },
        { label := "lem:fan-certificate", title := "Fan label packing and certificate-closed charge", nodeIds := [70] }
      ]
      declarationGroups := [{
        groupId := "fan-label-packing-ct9"
        title := "Framework-owned representative packing"
        role := .semanticTheorem
        explanation := "CT9 owns the exact capacity-one partition and global count. The graph layer owns the separately cached thirteen-position slot certificate and compatibility argument. The Erdős layer declares only the manuscript marked-fan label contract on actual ports."
        declarations := [
          `StructuralExhaustion.CT9.fibreCount_le_one_of_label_injective_on_items,
          `StructuralExhaustion.CT9.runBoundedOfLabelInjectiveOnItems,
          `StructuralExhaustion.Graph.P13PositionPacking.eq_or_positionDistance_eq_four_of_slot_eq,
          `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.run,
          `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.cardinality_le_eight,
          `Erdos64EG.Internal.MarkedFan.packingProfile,
          `Erdos64EG.Internal.MarkedFan.run,
          `Erdos64EG.Internal.MarkedFan.degree_le_eight,
          `Erdos64EG.Internal.exists_verifiedFanLabelPackingPrefix
        ]
      }]
      scopeNotes := "This implements the degree-at-most-eight clause of the manuscript lemma. The at-most-seven strengthening is implemented by the following CT9 stage; the certificate-closed charge calculation remains downstream."
      workBound := "CT9 scans eight fibres over exactly d(h) incident ports. The 13×13 slot certificate is isolated in its own compiled framework module. No one of the 8192 attachment codes, no subset family, and no graph universe is enumerated."
    },
    {
      stepId := "erdos.marked-fan-label-packing"
      stageId? := some "proof-slice.marked-fan-label-packing"
      title := "Non-singleton marked-fan cap"
      plainExplanation :=
        "Choose two distinct positions in the distinguished marked label. Their closed conflict neighbourhood blocks two different representative slots. The graph layer erases that one fan port, gives the blocked slots capacity zero and each other slot capacity one, and runs CT9. At most six other labels remain, so the full fan has degree at most seven."
      formalStatement :=
        "|S_h(u)|\\ge2 \\Longrightarrow d_G(h)\\le7"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:fan-certificate", title := "Fan label packing and certificate-closed charge", nodeIds := [70] }
      ]
      declarationGroups := [{
        groupId := "marked-fan-label-packing-ct9"
        title := "Framework-owned two-blocked-slot refinement"
        role := .semanticTheorem
        explanation := "The generic CT9 layer owns absent zero-capacity fibres and the bounded run. The graph layer owns erased-item bookkeeping, the cached blocked-slot certificate, exact capacity six, and the seven-member conclusion. The Erdős layer identifies the actual port and two positions."
        declarations := [
          `StructuralExhaustion.CT9.runBoundedOfBounded,
          `StructuralExhaustion.CT9.fibreCount_eq_zero_of_label_absent,
          `StructuralExhaustion.Graph.P13PositionPacking.secondSlot_blocked,
          `StructuralExhaustion.Graph.P13PositionPacking.sum_twoBlockedCapacity_eq_six,
          `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.run,
          `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.cardinality_le_seven,
          `Erdos64EG.Internal.NonSingletonMarkedFan.packingProfile,
          `Erdos64EG.Internal.NonSingletonMarkedFan.run,
          `Erdos64EG.Internal.NonSingletonMarkedFan.degree_le_seven,
          `Erdos64EG.Internal.exists_verifiedMarkedFanLabelPackingPrefix
        ]
      }]
      scopeNotes := "This completes the manuscript's at-most-seven packing clause. The subsequent certificate-closed charge calculation is implemented by the following CT14 stage."
      workBound := "The runtime CT9 scan has eight fibres over the actual fan list with one member erased. The separately cached constant certificate checks 2197 position triples and 64 slot pairs once; no 8192-code label universe or family universe is enumerated."
    },
    {
      stepId := "erdos.certificate-closed-fan-charge"
      stageId? := some "proof-slice.certificate-closed-fan-charge"
      title := "Certificate-closed fan charge"
      plainExplanation :=
        "CT14 scans every actual fan port and sums the cubic-closed indicator to obtain c. The remaining k-c ports are open. In quarter units the center contributes 11-4k, each closed port contributes -1, and each open port contributes at least 3, so the exact lower bound is 11-k-4c. The defining certificate-closed inequality 4c+k≤11 makes this nonnegative."
      formalStatement :=
        "4c+k\\le11 \\Longrightarrow (11-4k)-c+3(k-c)=11-k-4c\\ge0"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:fan-certificate", title := "Fan label packing and certificate-closed charge", nodeIds := [70] },
        { label := "def:typeB-multiclosed-residual", title := "Certificate-closed Type B fan", nodeIds := [71, 72] }
      ]
      declarationGroups := [{
        groupId := "certificate-closed-fan-charge-ct14"
        title := "Framework-owned exact fan charge ledger"
        role := .semanticTheorem
        explanation := "The graph layer computes cubic closure from the two literal non-center assigned incidences, computes the exact assigned-incidence quarter weight, and owns the finite closed/open CT14 scan and integer lower-bound arithmetic. The Erdős layer supplies its assignment and later proves the external-correction transfer to induced-core charge."
        declarations := [
          `StructuralExhaustion.CT14.run_terminal_capacity_of_complete,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.closedCount_le_card,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.count_partition,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.run,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.run_terminal,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower_eq,
          `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower_nonnegative,
          `StructuralExhaustion.Graph.AssignedFanCharge.cubicClosed_iff_both_assigned,
          `StructuralExhaustion.Graph.AssignedFanCharge.quarterCharge_eq_neg_one_of_cubicClosed,
          `StructuralExhaustion.Graph.AssignedFanCharge.quarterCharge_ge_three_of_not_cubicClosed,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.chargeProfile,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.stage,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.chargeExact,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.charge_nonnegative,
          `Erdos64EG.Internal.exists_verifiedCertificateClosedFanChargePrefix
        ]
      }]
      scopeNotes := "This completes the certificate-closed charge clause of the fan-certificate lemma. The positive-deficit hybrid entry is already locally verified, but its marked-fan degree input and the global B1/B2 bridge are not yet composed in one downstream stage."
      workBound := "CT14 makes a constant number of passes over exactly k actual incident ports. No subset of ports, cubic-closed assignment, attachment-label family, path, subgraph, context, or graph universe is enumerated."
    },
    {
      stepId := "erdos.positive-deficit-fan-entry"
      stageId? := some "proof-slice.positive-deficit-fan-entry"
      title := "Positive-deficit fan-closed entry"
      plainExplanation :=
        "Two compatible fan-closed ports give two distinct actual cubic-closed neighbours. The marked-fan CT9 theorem supplies k≤8 rather than accepting it as a local premise. Hence the exact quarter-deficit 4c+k-11 is positive, while the two real non-centre incidences of every cubic-closed neighbour form an endpoint-disjoint CT14 ledger whose half-credits pay that deficit with three quarter-units of slack."
      formalStatement :=
        "r\\ge2 \\Longrightarrow c\\ge2,\\quad 0<4c+k-11,\\quad 4c-(4c+k-11)\\ge3"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:fan-closed-port-typeB-routing", title := "Fan-closed ports route to the Type B fan ledger", nodeIds := [72] },
        { label := "lem:typeB-multiclosed-budget", title := "Positive-deficit fan-window budget", nodeIds := [72] },
        { label := "lem:typeB-hybrid-incidence-budget", title := "Hybrid incidence budget", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "positive-deficit-fan-entry-ct14"
        title := "Composed marked-fan and incidence CT14 stage"
        role := .semanticTheorem
        explanation := "The Erdős data are only the actual marked fan, assigned-incidence predicate, and two compatible fan-closed ports. The existing framework mass and hybrid-incidence profiles derive the closed count, positive deficit, exact CT14 execution, endpoint-disjoint credit, and work bound; the marked-fan degree theorem is consumed directly."
        declarations := [
          `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.massStage,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.degree_le_eight,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.two_le_closedCount,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.positiveDeficit,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybridStage,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_terminal,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays,
          `Erdos64EG.Internal.exists_verifiedPositiveDeficitFanEntryPrefix
        ]
      }]
      scopeNotes := "This composes the previously separate marked-fan degree cap and local hybrid incidence execution for the actual two-fan-closed-port branch. Global disjointness between entries belonging to different fan centres is the subsequent B2 problem and is not claimed here."
      workBound := "The mass and incidence CT14 stages use only the actual cubic-closed subtype and exactly two incidences per member, with the existing bound 4n²+20n+1. No port subsets, label families, candidate ledgers, paths, subgraphs, contexts, or graphs are enumerated."
    },
    {
      stepId := "erdos.local-b1-entry"
      stageId? := some "proof-slice.local-b1-entry"
      title := "Local hybrid fan entry realizes B1"
      plainExplanation :=
        "The positive-deficit CT14 result is converted to a framework semantic ledger containing exactly the five facts used by B1: terminal capacity, 2c literal incidences, injective endpoint carriers, the exact window/non-window partition, and payment of the total and residual demands."
      formalStatement :=
        "I_W+I_N=2c,\\quad \\operatorname{inj}(\\mathrm{carrier}),\\quad \\tfrac12(I_W+I_N)\\ge D_B,\\quad \\tfrac12I_N\\ge D_N"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-hybrid-B1", title := "Local hybrid fan entry", nodeIds := [72] },
        { label := "cor:typeB-local-entry-is-B1", title := "The local hybrid entry realizes B1", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "local-b1-entry-ct14"
        title := "Framework semantic B1 projection"
        role := .semanticTheorem
        explanation := "The graph framework projects an already verified CT14 stage to the local-ledger consumer interface. The Erdős theorem is only the fixed-profile instantiation and introduces no additional hypothesis."
        declarations := [
          `StructuralExhaustion.Graph.HybridFanIncidence.VerifiedStage.toLocalLedgerEntry,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1Entry,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1_endpoint_disjoint,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1_nonWindow_credit_pays,
          `Erdos64EG.Internal.exists_verifiedLocalB1Prefix
        ]
      }]
      scopeNotes := "This proves the local B1 identification only. Pairwise disjointness of carriers belonging to different fan centers is the subsequent finite B2 problem."
      workBound := "A proof-level projection of the existing CT14 stage; it performs no new scan and constructs no new finite universe."
    },
    {
      stepId := "erdos.positive-deficit-candidate"
      stageId? := some "proof-slice.positive-deficit-candidate"
      title := "Concrete positive-deficit candidate fibre"
      plainExplanation :=
        "A candidate is now a proved finite subset of the literal fan-incidence universe, rather than an application-supplied validity predicate. It must contain every packed-window incidence, avoid every incidence occupied by the ordinary reserve, and select enough non-window half-credits to pay the exact remaining demand. If the reserve occupies none of these incidences, the verified local B1 inequality constructs the all-incidence candidate."
      formalStatement :=
        "I_W\\subseteq S,\\quad S\\cap R_{\\mathrm{ord}}=\\varnothing,\\quad 2|S\\cap I_N|\\ge D_N"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-candidate-ledger", title := "Type B candidate entries", nodeIds := [72, 73] },
        { label := "lem:typeB-hybrid-B1", title := "Local hybrid fan entry", nodeIds := [72] }
      ]
      declarationGroups := [{
        groupId := "positive-deficit-candidate-ct14"
        title := "Framework-owned weighted finite selection"
        role := .semanticTheorem
        explanation := "The core defines finite mandatory/forbidden weighted selections without evaluating a powerset. The graph layer specializes the item universe and support to literal hybrid fan incidences. The Erdős layer is a thin instantiation."
        declarations := [
          `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.finite_candidate_fibre,
          `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.contains_every_window,
          `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.selected_reserve_free,
          `StructuralExhaustion.Graph.HybridFanCandidate.Candidate.nonWindow_payment,
          `StructuralExhaustion.Graph.HybridFanCandidate.allItems_weight_eq_nonWindowQuarterCredit,
          `StructuralExhaustion.Graph.HybridFanCandidate.allItemsCandidate,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.candidateProfile,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.candidate_nonWindow_payment,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.reserveFreeCandidate,
          `Erdos64EG.Internal.exists_verifiedPositiveDeficitCandidatePrefix
        ]
      }]
      scopeNotes := "This is the exact positive-deficit candidate fibre and a constructive sufficient existence case. It does not assume a candidate-validity contract. The certificate-closed candidate fibre and the cross-centre choice/overlap argument are the next stages."
      workBound := "The concrete all-incidence witness makes one linear pass over exactly 2c literal incidences. Finiteness is proved by an injective subtype argument over Finset; no powerset, candidate product, demand subset, path, subgraph, context, or graph universe is evaluated."
    },
    {
      stepId := "erdos.certificate-closed-candidate"
      stageId? := some "proof-slice.certificate-closed-candidate"
      title := "Concrete certificate-closed candidate fibre"
      plainExplanation :=
        "A candidate is a proved subset of the actual neighbour-port list. Its assigned-incidence weight is q=11-4(1+a). Decorative or packed-window incidences outside the counted core contribute an exact external correction, so Lean proves q+4e equals the actual induced-core quarter charge and hence q is a safe lower bound. The selected total offsets the exact center charge 11-4k. Reserve-used vertices are forbidden, and every selected endpoint is a literal adjacent degree-three non-center vertex."
      formalStatement :=
        "A_h ⊆ N(h) ∖ H_X,\\quad (11-4k)+\\sum_{v\\in A_h} q(v) \\ge 0"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-candidate-ledger", title := "Type B candidate entries", nodeIds := [72, 73] },
        { label := "lem:typeB-maximal-completion", title := "Finite completion of the Type B support assignment", nodeIds := [73] }
      ]
      declarationGroups := [{
        groupId := "certificate-closed-candidate-ct14"
        title := "Framework-owned exact fan-neighbour selection"
        role := .semanticTheorem
        explanation := "The graph layer computes assigned-degree member weights and owns the center demand, finite candidate subtype, reserve exclusion, carrier support, and complete-neighbour witness. The induced-core transfer, including exact external-shoulder correction, is proved separately from literal graph assignment. The Erdős layer identifies members with actual ports and derives the N(h) minus H_X condition from adjacency and deletion criticality."
        declarations := [
          `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItems_weight_ge,
          `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.Candidate.charge_nonnegative,
          `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.Candidate.selected_reserve_free,
          `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.candidateProfile,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_adjacent,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_endpoint_cubic,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.selected_endpoint_not_high,
          `Erdos64EG.Internal.CertificateClosedMarkedFan.reserveFreeCandidate,
          `Erdos64EG.Internal.exists_verifiedTypeBCandidateFibresPrefix
        ]
      }]
      scopeNotes := "Both local Type B candidate predicates are now concrete framework definitions. The next stage forms the actual dependent demand family from these two fibres and only then applies CT12."
      workBound := "The constructive witness scans exactly k actual fan ports. The candidate fibre is logically finite by the common subtype theorem; no powerset, candidate product, demand subset, path, subgraph, context, or graph universe is evaluated."
    },
    {
      stepId := "erdos.type-b-demand-system"
      stageId? := some "proof-slice.type-b-demand-system"
      title := "Concrete dependent Type B demand family"
      plainExplanation :=
        "A declared assigned support maps each center to either its certificate-closed local entry or its positive-B1 local entry. That branch value definitionally determines the literal item universe and weighted selection profile. The common adapter derives candidates, finiteness, selected support, and the complete declared support used by overlap."
      formalStatement :=
        "\\mathcal E(h)=\\{S\\subseteq I_h:\\operatorname{Valid}_h(S)\\},\\quad |\\mathcal D|\\le |V(G)|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-candidate-ledger", title := "Candidate Type B ledger entries", nodeIds := [72, 73] }
      ]
      declarationGroups := [{
        groupId := "type-b-dependent-selection"
        title := "Framework-derived heterogeneous ledger"
        role := .semanticTheorem
        explanation := "The core adapter owns the dependent candidate and support fields. The Erdős specialization only selects one already verified literal fan profile at each declared center."
        declarations := [
          `StructuralExhaustion.Core.DependentWeightedSelection.Profile.refinedLedger,
          `Erdos64EG.Internal.TypeBAssignedSupport.candidateFamily,
          `Erdos64EG.Internal.TypeBAssignedSupport.ledgerProfile,
          `Erdos64EG.Internal.TypeBAssignedSupport.candidate_finite,
          `Erdos64EG.Internal.TypeBAssignedSupport.demand_card_le_vertices,
          `Erdos64EG.Internal.TypeBAssignedSupport.demand_center_mem_declaredSupport,
          `Erdos64EG.Internal.exists_verifiedTypeBDemandSystemPrefix
        ]
      }]
      scopeNotes := "This is complete for every declared assigned-center family. Completeness of that family relative to a raw vertex support is proved separately by the high-center resolution split."
      workBound := "The schedule is a filtered subtype of the explicit vertex enumeration. Candidate finiteness is proof-level; declared support scans each local item list once. No candidate product or demand powerset is evaluated."
    },
    {
      stepId := "erdos.type-b-completion"
      stageId? := some "proof-slice.type-b-completion"
      title := "CT12 full choice or minimal overlap"
      plainExplanation :=
        "CT12 peels the entire declared center schedule. If all demands admit mutually disjoint candidates, Lean returns a full dependent choice. Otherwise it proves a nonempty full obstruction and selects a least-cardinality obstructing subschedule, every proper shorter nonempty subschedule of which has a disjoint choice."
      formalStatement :=
        "\\operatorname{FullChoice}(\\mathcal D)\\ \\lor\\ \\exists\\varnothing\\ne\\mathcal O\\subseteq\\mathcal D\\;\\operatorname{MinimalOverlap}(\\mathcal O)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-maximal-completion", title := "Finite completion of the Type B support assignment", nodeIds := [73] },
        { label := "lem:typeB-bridge-to-overlap", title := "Bridge failure produces a minimal overlap obstruction", nodeIds := [73] }
      ]
      declarationGroups := [{
        groupId := "type-b-ct12-completion"
        title := "Unconditional refined-ledger CT12"
        role := .semanticTheorem
        explanation := "The framework treats the empty schedule by its vacuous choice and the nonempty failure by an exact obstruction. Nat.find proves minimality without evaluating subfamilies."
        declarations := [
          `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.fullChoice_or_obstruction,
          `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.exists_minimal_obstruction,
          `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.fullChoice_or_minimal_obstruction,
          `StructuralExhaustion.CT12.RefinedLedgerCompletion.Profile.verifiedStage,
          `Erdos64EG.Internal.TypeBAssignedSupport.completionStage,
          `Erdos64EG.Internal.TypeBAssignedSupport.full_choice_or_minimal_obstruction,
          `Erdos64EG.Internal.TypeBAssignedSupport.completion_iterations_le_vertices,
          `Erdos64EG.Internal.exists_verifiedTypeBCompletionPrefix
        ]
      }]
      scopeNotes := "This proves completeness of the fixed declared demand schedule. It intentionally does not identify that statement with residual-core maximality or decorated-handoff closure."
      workBound := "Exactly one list-peeling iteration per declared center and therefore at most |V(G)| iterations. Choice and minimality are proof-level; candidate products and demand subsets are never materialized."
    },
    {
      stepId := "erdos.type-b-overlap"
      stageId? := some "proof-slice.type-b-overlap"
      title := "Minimal overlap support and inherited graph constraints"
      plainExplanation :=
        "On failure of the full choice, the exact CT12 obstruction is packaged with the union of the declared carrier universes of its demands. This union retains a reserve-blocked demand even if it has no valid candidate. Every demand center lies in the union; ambient target avoidance, independence of high centers, cubicity of their neighbours, and proper-subfamily ledger choices are proved directly."
      formalStatement :=
        "\\neg\\operatorname{FullChoice}\\Rightarrow\\exists\\mathcal O\\;[\\operatorname{MinimalOverlap}(\\mathcal O)\\land H_{\\mathcal O}\\subseteq Z(\\mathcal O)]"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:typeB-overlap-obstruction", title := "Minimal Type B overlap obstruction", nodeIds := [73] },
        { label := "lem:typeB-global-local-reflection", title := "Global-to-local reflection of Type B overlap", nodeIds := [73] }
      ]
      declarationGroups := [{
        groupId := "type-b-overlap-support"
        title := "Exact support and unconditional reflection clauses"
        role := .semanticTheorem
        explanation := "The framework support is derived from each finite weighted profile, not supplied by an application certificate. The Erdős layer applies existing target avoidance and deletion-criticality theorems."
        declarations := [
          `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.declaredCarrierSupport,
          `StructuralExhaustion.Core.FiniteWeightedSelection.Profile.carrierSupport_subset_declared,
          `Erdos64EG.Internal.TypeBAssignedSupport.minimalOverlap_of_no_fullChoice,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_disjoint_choice,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.center_mem_carrierSet,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.ambient_dyadic_safe,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.centers_not_adjacent,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.center_neighbor_cubic,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.sameWindow_directCycleFree,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.twoWindow_directCycleFree,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_compression_impossible,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_separated_carrier_partition,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_subschedule_has_choice,
          `Erdos64EG.Internal.exists_verifiedTypeBOverlapSupportPrefix
        ]
      }]
      scopeNotes := "The exact support, contextual target avoidance, high-center separation, cubic-neighbour clause, both direct window exclusions, literal nonempty-boundary CT3 compression exclusion, minimal-overlap clause, and impossibility of a carrier-separated demand split are proved. Turning the last combinatorial theorem into induced-graph connectivity, plus the window-stub global count and delocalization routing, requires additional graph structures."
      workBound := "Support construction is linear in the declared local item universes. Minimal obstruction selection is proof-level Nat.find and performs no subfamily enumeration."
    },
    {
      stepId := "erdos.type-b-resolution"
      stageId? := some "proof-slice.type-b-resolution"
      title := "Total high-center state-space stratification"
      plainExplanation :=
        "Starting only from a literal vertex support and reserve, Lean filters all high centers. Either one actual center has no certificate-closed or positive-B1 local entry, or proof-level finite choice builds the complete assigned family and CT12 returns a full disjoint ledger or a minimal overlap obstruction. Thus local-entry existence is no longer silently accepted as a support field."
      formalStatement :=
        "(\\exists h\\in V_{\\ge4}(X),\\ \\mathcal E(h)=\\varnothing)\\ \\lor\\ \\operatorname{FullChoice}\\ \\lor\\ \\operatorname{MinimalOverlap}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-bridge-statements", title := "Type B bridge statements", nodeIds := [73, 74] },
        { label := "prop:typeB-global-local-bridge", title := "Type B bridge residual as a global-to-local obstruction", nodeIds := [73, 74] }
      ]
      declarationGroups := [{
        groupId := "type-b-total-resolution"
        title := "Framework finite resolution and Erdős high-center specialization"
        role := .semanticTheorem
        explanation := "The generic core proves witness-at-every-site versus a literal unresolved site. The application derives its sites by filtering the graph's finite vertex support at ambient degree four."
        declarations := [
          `StructuralExhaustion.Core.FiniteResolution.Profile.fullResolution_or_unresolved,
          `Erdos64EG.Internal.TypeBSupportScope.highCenters,
          `Erdos64EG.Internal.TypeBSupportScope.center_high,
          `Erdos64EG.Internal.TypeBSupportScope.assignedSupport,
          `Erdos64EG.Internal.TypeBSupportScope.unresolved_or_fullChoice_or_minimalOverlap,
          `Erdos64EG.Internal.exists_verifiedTypeBResolutionPrefix
        ]
      }]
      scopeNotes := "This closes the completeness gap for ordinary high-center demands in a supplied vertex scope. A local-entry failure is an explicit theorem branch, not an assumed contract. The distinct decorated-handoff and later fan-mass closures remain separate manuscript branches."
      workBound := "The high-center schedule is a linear filter of the explicit vertex enumeration. The dependent resolution and choice split are proof-level and do not enumerate witness products."
    },
    {
      stepId := "erdos.type-b-assigned-charge"
      stageId? := some "proof-slice.type-b-assigned-charge"
      title := "Exact Type B graph-charge realization"
      plainExplanation :=
        "For a full disjoint local choice, Lean names the exact core vertices consumed at every center. Certificate weights transfer to selected core neighbours; window credit transfers through external assigned shoulders; selected non-window credit transfers only through canonical ordinary available vertices. These supports lie inside the candidate carriers, so CT12 disjointness prevents reuse. The graph layer then partitions the counted core into used vertices, retained high centers, and the remaining core and proves the exact reduced-ledger identity. Separately, deleting all actual high centers gives the choice-free receiver-overload bound on every literal Type B scope."
      formalStatement :=
        "4\\operatorname{No}(X)=B_{\\mathrm{selected}}+4\\sum_{h\\in H_X}\\delta_X^+(h)+B_{\\mathrm{remaining}},\\qquad -4\\operatorname{No}(X)\\le 21S_X+\\Omega_A(X)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-candidate-ledger", title := "Candidate Type B ledger entries", nodeIds := [72, 73] },
        { label := "lem:typeB-exact-postledger", title := "Exact post-B2 charge decomposition", nodeIds := [73, 74] },
        { label := "lem:typeB-postledger-core-hygiene", title := "Post-ledger Type A boundary identity", nodeIds := [74] },
        { label := "def:typeB-center-deleted-overload", title := "Center-deleted Type A overload", nodeIds := [74] },
        { label := "prop:typeB-unconditional-deficit", title := "Unconditional Type B deficit bound", nodeIds := [74] },
        { label := "prop:typeB-bridge-reduction", title := "Quantitative Type B reduction under the refined ledger", nodeIds := [74] }
      ]
      declarationGroups := [{
        groupId := "type-b-exact-assigned-charge"
        title := "Framework graph ledger and Erdős literal transfer"
        role := .semanticTheorem
        explanation := "The reusable graph profile owns the exact post-selection partition and reduced-ledger algebra. The application proves that its local candidate resources are literal, core-contained, center-free subsets of the framework carriers."
        declarations := [
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.coreQuarterCharge_eq_used_add_centers_add_remaining,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.centerCoreCharge_add_card_nonnegative,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.netQuarterCharge_nonnegative_or_remaining_negative,
          `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.quarterCharge_nonnegative,
          `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.neg_quarterCharge_le_totalOverload,
          `StructuralExhaustion.Core.FiniteReceiverDischarge.Routing.saturated_or_unsaturated,
          `StructuralExhaustion.Core.FiniteBoundaryTransfer.Profile.transfer_or_overloaded,
          `StructuralExhaustion.Graph.LowDegreeReceiverRouting.FiniteObject.exists_reachable_receiver,
          `StructuralExhaustion.Graph.FiniteInducedBoundary.Profile.exists_incidence_of_loss_pos,
          `StructuralExhaustion.Graph.HighCenterDeletionCharge.Profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload,
          `StructuralExhaustion.Graph.WindowExternalCharge.windowQuarterCredit_le_externalCorrection,
          `StructuralExhaustion.Graph.InducedCoreFanReserve.incidence_free_ordinary_of_nonWindow,
          `StructuralExhaustion.Core.FiniteRefinedLedger.Profile.Choice.refinedSupport_pairwiseDisjoint,
          `Erdos64EG.Internal.TypeBAssignedSupport.actualCoreSupport_subset_carrierSupport,
          `Erdos64EG.Internal.TypeBAssignedSupport.fullActualCoreSupport_pairwiseDisjoint,
          `Erdos64EG.Internal.TypeBAssignedSupport.fullLocalQuarterBalance_le_actualCharge,
          `Erdos64EG.Internal.TypeBAssignedSupport.processedFanCharge_nonnegative,
          `Erdos64EG.Internal.TypeBAssignedSupport.netQuarterCharge_nonnegative_or_remaining_negative,
          `Erdos64EG.Internal.TypeBAssignedSupport.remainingInducedQuarterCharge_eq_raw_add_boundary,
          `Erdos64EG.Internal.TypeBAssignedSupport.netQuarterCharge_nonnegative_of_unsaturated_boundaryTransfer,
          `Erdos64EG.Internal.TypeBAssignedSupport.boundaryOverload_has_landing,
          `Erdos64EG.Internal.TypeBLocalEntry.actualCoreSupport_card_le_twentyFour,
          `Erdos64EG.Internal.TypeBAssignedSupport.processedDegreeSum_le_twoHundred_mul_centers,
          `Erdos64EG.Internal.TypeBAssignedSupport.neg_netQuarterCharge_le_eightHundred_mul_assignedSurplus_of_unsaturated,
          `Erdos64EG.Internal.TypeBSupportScope.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_receiverOverload,
          `Erdos64EG.Internal.TypeBSupportScope.unresolved_or_overlap_or_net_nonnegative_or_saturated_or_bounded_boundaryOverload,
          `Erdos64EG.Internal.exists_verifiedTypeBPostLedgerPrefix
        ]
      }]
      scopeNotes := "The official quantitative endpoint is choice-free: unresolved local entries and B2 overlap cannot evade the charge bound. The only remaining term is the exact total overload of the proof-selected receiver fibres in the literal center-deleted Type A graph. The finer full-choice theorem and its 800-unit selected-envelope bound remain valid refinements, not assumptions in the unconditional result."
      workBound := "All constructions are proof-level finset images, filters, unions, sums, and monotone Fin embeddings over declared centers, ports, selected incidences, and the actual remaining vertex set. No powerset, injection space, candidate product, graph family, path family, or context universe is evaluated."
    },
    {
      stepId := "erdos.sparse-envelope"
      stageId? := some "proof-slice.sparse-envelope"
      title := "Sparse upper envelope and slack identity"
      plainExplanation :=
        "A cubic vertex is obtained from the already verified deletion-critical graph. Every induced core in its complement is a proper subgraph of the selected counterexample, so the no-proper-core theorem produces a two-degenerate elimination certificate. CT12 checks precisely that finite order. Counting at most two deleted edges until the last two vertices gives e(G-v)≤2(n-1)-3; restoring the three incident edges gives m≤2n-2. The graph handshake theorem identifies the CT6 excess ledger with σ=2m-3n, and elementary integer algebra gives σ=n-6-2λ."
      formalStatement :=
        "m\\le 2n-2,\\qquad \\lambda=2n-3-m,\\qquad \\sigma=2m-3n=n-6-2\\lambda"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:sparse-upper-envelope", title := "Sparse upper envelope", nodeIds := [126] },
        { label := "lem:sparse-slack-surplus", title := "Sparse slack identity", nodeIds := [126] }
      ]
      declarationGroups := [{
        groupId := "sparse-envelope-ct12"
        title := "Two-degenerate graph profile, exact CT12 run, and Erdős arithmetic"
        role := .semanticTheorem
        explanation := "The reusable graph layer proves existence of the bounded elimination order from local induced-core freeness, executes CT12 on that list, proves the sharp edge count, and connects the ordered degree-excess total to the handshake identity. The Erdős layer supplies only the selected cubic vertex and the concrete no-proper-core specialization."
        declarations := [
          `StructuralExhaustion.Graph.DegeneracyPeeling.exists_certificate_of_internalMinDegreeFree,
          `StructuralExhaustion.Graph.DegeneracyPeeling.edgeCount_le_two_mul_vertexCount_sub_three,
          `StructuralExhaustion.Graph.DegeneracyPeeling.Profile.verifiedStage,
          `StructuralExhaustion.Graph.SurplusPortActivity.degreeExcess_sum_int_eq,
          `Erdos64EG.Internal.sparseEnvelopeProfile,
          `Erdos64EG.Internal.sparseEnvelopeRoot_degree,
          `Erdos64EG.Internal.sparseEnvelopeRemaining_coreFree,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_terminal,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_trace,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_verified,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_traceValid,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_total,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_iterations,
          `Erdos64EG.Internal.runSparseEnvelopeCT12_linearBudget,
          `Erdos64EG.Internal.sparseEnvelopeRemaining_edgeBound,
          `Erdos64EG.Internal.sparseEnvelope_edgeBound,
          `Erdos64EG.Internal.sparseSlack_surplus_identity,
          `Erdos64EG.Internal.sparseEdge_surplus_identity,
          `Erdos64EG.Internal.sparseSurplus_eq_degreeExcessLedger,
          `Erdos64EG.Internal.exists_verifiedSparseEnvelopePrefix
        ]
      }]
      scopeNotes := "This verifies the complete node [126] block, including both displayed identities. Nodes [127]–[128] remain the already verified CT6 surplus/activation outputs; the first later sparse-branch datum not yet implemented is node [129]'s baseline spine demand."
      workBound := "CT12 performs exactly n-1 peeling iterations on one proof-selected vertex list and has a linear polynomial check budget. The edge theorem uses well-founded recursion on strictly smaller explicit supports; no graph, subgraph, order, path, or context universe is enumerated."
    },
    {
      stepId := "erdos.baseline-spine-demand"
      title := "Baseline spine demand"
      plainExplanation := "The next sparse-branch step fixes the node [129] linear deficit demand consumed by the active surplus family."
      formalStatement := "D_{\\mathrm{base}}=O(n)"
      status := .next
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:baseline-spine-demand", title := "Baseline spine demand", nodeIds := [129] }
      ]
      scopeNotes := "The sparse envelope, exact slack identity, and the existing CT6 active surplus ledger are verified. The baseline demand and its subsequent response/token routing are not yet implemented."
      workBound := "Not yet implemented; the future CT must expose its local finite universe and polynomial audit."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "erdos-64"
  title := "Erdős Problem 64"
  summary :=
    "A partial proof with exact Mersenne returns, lexicographic minimal selection, CT2 criticality and bridge contraction, CT3 boundaried uncompressibility, an HSS-forced induced-P13 CT1 stage, a routed maximum-packing CT12 remainder stage, the complete CT10 P13 attachment-label algebra, a polynomial ordered CT6 degree-surplus ledger, a routed CT9 surplus-pair split, framework-native local-port verification, concrete Type B candidate fibres, an unconditional dependent CT12 choice-or-minimal-overlap theorem, an exact high-center local-resolution trichotomy, a no-double-counted induced-core realization of the full Type B charge ledger, and the choice-free Type B receiver-overload deficit bound."
  proofStatus := .partialProof
  workflows := [proofSliceWorkflow]
  interfaceBindings := [
    {
      bindingId := "proof-slice.ct1-target"
      stageId := "proof-slice.ct1"
      tacticId := "CT1"
      role := "Mersenne return target encoding"
      description := "A rooted return is the positive code and exact return-set disjointness supplies the avoiding execution."
      problemDeclaration := `Erdos64EG.Internal.mersenneReturnEncoding
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.edgeRootedEncoding
    },
    {
      bindingId := "proof-slice.ct2-proper-core"
      stageId := "proof-slice.no-proper-core"
      tacticId := "CT2"
      role := "certificate-driven proper-subgraph reduction"
      description := "The application supplies one finite proper-subgraph certificate; the framework proves rank decrease, runs the canonical deletion-C2 path, and exposes a constant work bound."
      problemDeclaration := `Erdos64EG.Internal.packedStaticInput
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run
    },
    {
      bindingId := "proof-slice.ct2-deletion"
      stageId := "proof-slice.ct2"
      tacticId := "CT2"
      role := "single-dart deletion capability"
      description := "The local capability supplies finite dart discovery, graph deletion, rank decrease, baseline preservation, and target transport."
      problemDeclaration := `Erdos64EG.Internal.routedProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.edgeRootedDeletionPrefix
    },
    {
      bindingId := "proof-slice.ct3-boundaried-replacement"
      stageId := "proof-slice.ct3"
      tacticId := "CT3"
      role := "literal target-complete graph replacement"
      description := "A local representative supplies boundary response, internal degree, and local smallness; literal gluing derives whole-rank decrease, baseline preservation, and target transport before the minimality contradiction."
      problemDeclaration := `Erdos64EG.Internal.packedStaticInput
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
    },
    {
      bindingId := "proof-slice.ct1-induced-p13"
      stageId := "proof-slice.induced-p13"
      tacticId := "CT1"
      role := "certificate-driven induced-path realization"
      description := "The problem supplies the fixed path order thirteen and the HSS closure of the avoiding branch; the graph layer owns the embedding certificate, both exact CT1 executions, totality, and constant work bounds."
      problemDeclaration := `Erdos64EG.Internal.inducedP13Profile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.InducedPath.Profile.encoding
    },
    {
      bindingId := "proof-slice.ct12-p13-packing"
      stageId := "proof-slice.p13-packing"
      tacticId := "CT12"
      role := "maximum disjoint induced-path packing"
      description := "The problem fixes path order thirteen; the core selects a maximum support-disjoint family, CT12 audits exactly its selected list, and the graph layer derives saturation, the induced-path-free remainder, and the arbitrary-subgraph minimum-degree bridge."
      problemDeclaration := `Erdos64EG.Internal.inducedP13PackingProfile
      frameworkDeclaration :=
        `StructuralExhaustion.CT12.DisjointPacking.Profile.verifiedStage
    },
    {
      bindingId := "proof-slice.ct12-sparse-envelope"
      stageId := "proof-slice.sparse-envelope"
      tacticId := "CT12"
      role := "two-degenerate elimination order"
      description := "The application proves induced-core freeness of the cubic-vertex complement. The graph profile selects one bounded elimination certificate, and CT12 audits exactly that finite list with linear work."
      problemDeclaration := `Erdos64EG.Internal.sparseEnvelopeProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.DegeneracyPeeling.Profile.verifiedStage
    },
    {
      bindingId := "proof-slice.ct10-p13-labels"
      stageId := "proof-slice.p13-labels"
      tacticId := "CT10"
      role := "exact finite attachment-label classification"
      description := "The problem supplies a compact thirteen-bit legality predicate proved equivalent to graph-theoretic cycle avoidance; the generic CT10 profile classifies the 8192 local candidates, audits the complete 399-row table, and retains a quadratic work certificate."
      problemDeclaration := `Erdos64EG.Internal.p13AttachmentClassification
      frameworkDeclaration :=
        `StructuralExhaustion.CT10.ExhaustiveClassification.Profile.verifiedStage
    },
    {
      bindingId := "proof-slice.ct1-triangular-return"
      stageId := "proof-slice.triangular-port-return"
      tacticId := "CT1"
      role := "certificate-driven triangular-port return"
      description := "The application supplies only the power-of-two target interpretation; the framework consumes CT2 bridgelessness, derives the shoulder path and cycle certificate, and executes one proof-carrying CT1 check."
      problemDeclaration := `Erdos64EG.Internal.triangularPortReturnStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.TriangularPortReturn.verifiedStage
    },
    {
      bindingId := "proof-slice.ct10-triangular-first-landing"
      stageId := "proof-slice.triangular-first-landing"
      tacticId := "CT10"
      role := "exact shoulder-completion landing classification"
      description := "The application supplies only the already verified selected graph. The graph layer enumerates the explicit completion-incidence table, proves central/cross/outside semantics, and composes the CT10 result with the preceding CT1 return."
      problemDeclaration := `Erdos64EG.Internal.triangularFirstLandingStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.TriangularFirstLanding.verifiedStage
    },
    {
      bindingId := "proof-slice.ct9-triangular-cross-shoulder"
      stageId := "proof-slice.triangular-cross-shoulder"
      tacticId := "CT9"
      role := "capacity-one cross-shoulder fibre"
      description := "The application selects two distinct triangular ports. The framework enumerates their four shoulder pairs, executes CT9, and turns overload into the high-shoulder branch or the forbidden four-cycle."
      problemDeclaration := `Erdos64EG.Internal.triangularCrossShoulderStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.TriangularCrossShoulder.verifiedStage
    },
    {
      bindingId := "proof-slice.ct5-fan-closed-port"
      stageId := "proof-slice.fan-closed-port"
      tacticId := "CT5"
      role := "four-incidence fan-closure ledger"
      description := "The application supplies the literal P13 window/remainder partition, an assigned-incidence predicate, and its four assignment facts. The framework computes support classes and derives both fan-closure conclusions, carrier distinctness, execution trace, totality, and the exact ten-check bound."
      problemDeclaration := `Erdos64EG.Internal.fanClosedPairStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.FanClosedPort.verifiedStage
    },
    {
      bindingId := "proof-slice.ct14-fan-closed-mass"
      stageId := "proof-slice.fan-closed-mass"
      tacticId := "CT14"
      role := "actual cubic-closed mass ledger"
      description := "The application supplies its P13 window/remainder and assigned-incidence predicates. The framework routes the actual CT5 charge residual to CT14, scans the semantic cubic-closed-neighbour subtype, and proves exact multiplicity, the compatible-pair lower bound, positive deficit, trace, totality, and polynomial work."
      problemDeclaration := `Erdos64EG.Internal.fanClosedMassStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.FanClosedPortMass.verifiedStage
    },
    {
      bindingId := "proof-slice.ct14-hybrid-fan-incidence"
      stageId := "proof-slice.hybrid-fan-incidence"
      tacticId := "CT14"
      role := "two-per-member hybrid incidence ledger"
      description := "The application supplies only its P13 profile and the marked-fan bound k≤8. The framework routes the actual CT14 capacity residual, constructs two literal non-centre incidences per cubic-closed member, proves endpoint disjointness and exact window/non-window multiplicities, and verifies the quarter-unit budget."
      problemDeclaration := `Erdos64EG.Internal.hybridFanIncidenceStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage
    },
    {
      bindingId := "proof-slice.ct1-direct-fan-window"
      stageId := "proof-slice.direct-fan-window"
      tacticId := "CT1"
      role := "same-window direct-cycle elimination"
      description := "The application supplies only its selected target-avoiding context. The graph layer turns every exact closed-pair violation into a literal simple cycle and derives direct-cycle-freeness through the zero-check CT1 avoiding execution."
      problemDeclaration := `Erdos64EG.Internal.directFanWindowStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.FanWindowCycle.verifiedAvoidingStage
    },
    {
      bindingId := "proof-slice.ct1-two-window-cycle"
      stageId := "proof-slice.two-window-cycle"
      tacticId := "CT1"
      role := "two-window direct-cycle elimination"
      description := "The graph layer joins two vertex-disjoint induced windows with symbolic orientation-independent bridges and derives the exact target exclusion through the zero-check CT1 avoiding execution."
      problemDeclaration := `Erdos64EG.Internal.twoWindowCycleStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.TwoWindowCycle.verifiedAvoidingStage
    },
    {
      bindingId := "proof-slice.ct9-fan-label-packing"
      stageId := "proof-slice.fan-label-packing"
      tacticId := "CT9"
      role := "certificate-marked fan representative packing"
      description := "The application supplies legal pairwise-compatible labels on actual incident ports. The framework chooses representatives, runs the fixed eight-fibre capacity-one audit, and derives degree at most eight."
      problemDeclaration := `Erdos64EG.Internal.MarkedFan.packingProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.P13FanLabelPacking.Profile.run
    },
    {
      bindingId := "proof-slice.ct9-marked-fan-label-packing"
      stageId := "proof-slice.marked-fan-label-packing"
      tacticId := "CT9"
      role := "non-singleton marked-fan refinement"
      description := "The application identifies one actual marked port and two positions in its label. The framework blocks two slots, runs CT9 on the erased list, and derives degree at most seven."
      problemDeclaration :=
        `Erdos64EG.Internal.NonSingletonMarkedFan.packingProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.P13MarkedFanLabelPacking.Profile.run
    },
    {
      bindingId := "proof-slice.ct14-certificate-closed-fan-charge"
      stageId := "proof-slice.certificate-closed-fan-charge"
      tacticId := "CT14"
      role := "certificate-closed marked-fan charge"
      description := "The application supplies the assigned-incidence relation on actual ports and its defining branch inequality. The framework computes assigned cubic closure and its exact local weight; the later assigned-support stage proves the transfer to literal induced-core charge."
      problemDeclaration :=
        `Erdos64EG.Internal.CertificateClosedMarkedFan.chargeProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.CertificateClosedFanCharge.Profile.run
    },
    {
      bindingId := "proof-slice.ct14-positive-deficit-fan-entry"
      stageId := "proof-slice.positive-deficit-fan-entry"
      tacticId := "CT14"
      role := "marked positive-deficit hybrid incidence entry"
      description := "The application supplies an actual marked fan and two assigned compatible fan-closed ports. The graph framework composes the existing CT14 mass and incidence runners with the derived marked-fan cap."
      problemDeclaration :=
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybridStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage
    },
    {
      bindingId := "proof-slice.ct14-local-b1-entry"
      stageId := "proof-slice.local-b1-entry"
      tacticId := "CT14"
      role := "local hybrid fan B1 ledger"
      description := "The application projects its verified positive-deficit stage to the graph-owned semantic local-ledger interface used verbatim by manuscript B1."
      problemDeclaration :=
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.localB1Entry
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.HybridFanIncidence.VerifiedStage.toLocalLedgerEntry
    },
    {
      bindingId := "proof-slice.ct14-positive-deficit-candidate"
      stageId := "proof-slice.positive-deficit-candidate"
      tacticId := "CT14"
      role := "concrete positive-deficit Type B candidate"
      description := "The application supplies its fixed fan profile and ordinary-reserve predicate. The framework defines the exact mandatory, forbidden, weighted candidate fibre and derives the all-incidence witness from the verified B1 payment inequality when the reserve is locally free."
      problemDeclaration :=
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.candidateProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.HybridFanCandidate.allItemsCandidate
    },
    {
      bindingId := "proof-slice.ct14-certificate-closed-candidate"
      stageId := "proof-slice.certificate-closed-candidate"
      tacticId := "CT14"
      role := "concrete certificate-closed Type B candidate"
      description := "The application identifies the actual port endpoints and high center. The framework turns the exact CT14 charge ledger into the weighted finite candidate fibre, and deletion criticality proves the selected endpoints lie outside the high-center set."
      problemDeclaration :=
        `Erdos64EG.Internal.CertificateClosedMarkedFan.candidateProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.CertificateClosedFanCandidate.Profile.allItemsCandidate
    },
    {
      bindingId := "proof-slice.ct12-type-b-completion"
      stageId := "proof-slice.type-b-completion"
      tacticId := "CT12"
      role := "dependent Type B full-choice or minimal-overlap completion"
      description := "The application supplies the literal branch-specific local profiles at each declared center. The framework derives heterogeneous candidate/support fields, peels the whole schedule, and proves the exact choice-or-obstruction alternative without evaluating a product or powerset."
      problemDeclaration :=
        `Erdos64EG.Internal.TypeBAssignedSupport.completionStage
      frameworkDeclaration :=
        `StructuralExhaustion.CT12.RefinedLedgerCompletion.Profile.verifiedStage
    }
  ]
  manuscript? := some erdosManuscript
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `Erdos64EG `Erdos64EG.WebExport.descriptor descriptor

end Erdos64EG.WebExport
