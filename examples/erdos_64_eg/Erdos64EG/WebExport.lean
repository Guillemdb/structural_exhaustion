import Erdos64EG
import Erdos64EG.Tests
import StructuralExhaustion.Canonical.ExampleExport

namespace Erdos64EG.WebExport

open StructuralExhaustion.Canonical

private def proofSliceWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "proof-slice"
  title := "Verified Erdős 64 prefix"
  purpose :=
    "Inspect the exact Mersenne target algebra, lexicographic minimal selection, CT2 criticality and bridge contraction, boundaried replacement, the HSS-forced induced-P13 CT1 stage, the routed maximum-packing CT12 remainder stage, the exhaustive CT10 P13 attachment-label algebra, the ordered CT6 degree-surplus ledger with per-slot activation, the CT15 baseline and free/blocked pair-response stages, the CT9 free-anchor and capacity-token ledgers, the exact 25-role coupled overload decision, and the Type B development through its graph-derived high-center choice/overlap trichotomy."
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
        `StructuralExhaustion.Core.IsCounterexample,
        `StructuralExhaustion.Core.target_of_not_isCounterexample,
        `Erdos64EG.Internal.IsCounterexample,
        `Erdos64EG.Internal.officialConclusion_of_notCounterexample,
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
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate.contextAudit,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.impossible,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.terminal,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.trace,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.checks,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.polynomial,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.total,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.route,
        `Erdos64EG.Internal.boundariedReplacementPrefix_previous,
        `Erdos64EG.Internal.boundariedReplacementPrefix_uncompressible,
        `Erdos64EG.Internal.verifiedRankDropRoutingStage,
        `Erdos64EG.Internal.rankDropRoutingPrefix_previous,
        `Erdos64EG.Internal.rankDropRoutingPrefix_stage
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
        `StructuralExhaustion.Graph.InducedPathPacking.remainder_card_ge_of_packingNumber_le,
        `Erdos64EG.Internal.P13CoverageResidual,
        `Erdos64EG.Internal.verifiedP13RemainderResidual,
        `Erdos64EG.Internal.p13Remainder_large,
        `Erdos64EG.Internal.p13Remainder_node26_exact,
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
      stageId := "proof-slice.surplus-scale-split"
      title := "Exact quadratic surplus-scale split"
      summary := "The actual degree surplus is compared with the squared fixed homogeneous-cap scale by one natural-number comparison, giving the exhaustive node-[19] non-near-cubic or bounded branch."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSurplusScaleRoutingPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.QuadraticScaleSplit.decide,
        `StructuralExhaustion.Core.QuadraticScaleSplit.exhaustive,
        `StructuralExhaustion.Core.QuadraticScaleSplit.verifiedStage,
        `Erdos64EG.Internal.surplusScaleCoefficient,
        `Erdos64EG.Internal.surplusScaleInput,
        `Erdos64EG.Internal.surplusScaleStage,
        `Erdos64EG.Internal.surplusScale_exhaustive,
        `Erdos64EG.Internal.routeSurplusScale,
        `Erdos64EG.Internal.routeSurplusScale_exhaustive,
        `Erdos64EG.Internal.verifiedSurplusScaleRoutingPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-positive-deficiency"
      title := "Exact P13-remainder positive deficiency"
      summary := "The graph-owned induced-support charge profile is instantiated on the exact selected P13 remainder, so node [28] is definitionally the sum of max(0,3-d_R(v)) on that same graph."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.internalDegree,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.positiveDeficiency,
        `Erdos64EG.Internal.p13RemainderDeficiencyProfile,
        `Erdos64EG.Internal.p13Remainder_internalDegree_eq,
        `Erdos64EG.Internal.p13Remainder_positiveDeficiency_eq
      ]
    },
    {
      stageId := "proof-slice.p13-multiscale-curvature"
      title := "CT10 complete multi-scale P13 curvature table"
      summary := "The bounded node-[19] constructor executes the complete 91-barrier finite relation certificate; the strict constructor is preserved for Part X."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.routeSurplusScaleThroughCurvature_exhaustive
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13CodeCompatibleSparse_iff,
        `Erdos64EG.Internal.p13CodeCompatibleFast_iff,
        `Erdos64EG.Internal.p13MultiScaleRows_codeAudit,
        `Erdos64EG.Internal.p13MultiScaleCompatibilityRow_semantic,
        `StructuralExhaustion.Core.FiniteBitRelationBarrier.Profile.safeCount,
        `StructuralExhaustion.Core.FiniteBitRelationBarrier.Profile.flatCount,
        `Erdos64EG.Internal.p13MultiScaleSafeCounts_audit,
        `Erdos64EG.Internal.p13MultiScaleFlatCounts_audit,
        `Erdos64EG.Internal.p13BarrierSafeCount_audit,
        `Erdos64EG.Internal.p13BarrierFlatCount_audit,
        `Erdos64EG.Internal.p13Barrier_class_count,
        `Erdos64EG.Internal.p13Barrier_one_one_counts,
        `Erdos64EG.Internal.p13MultiScaleBarrier_more_than_118_bits,
        `Erdos64EG.Internal.verifiedP13MultiScaleCurvaturePrefix,
        `Erdos64EG.Internal.routeSurplusScale,
        `Erdos64EG.Internal.routeSurplusScaleThroughCurvature
      ]
    },
    {
      stageId := "proof-slice.p13-actual-attachment-cold-fork"
      title := "Pointwise actual P₁₃ attachment cold fork"
      summary := "For one exact selected window, the finite actual outside-vertex-by-thirteen adjacency classifier cannot be hot and therefore returns its canonical missing assignment on that same window."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.p13ActualAttachment_classify_cold
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13ActualAttachmentSystem_value_eq_true_iff,
        `Erdos64EG.Internal.p13ActualAttachmentSystem_coordinateCard,
        `Erdos64EG.Internal.p13RawAttachmentSystem_hot_impossible,
        `Erdos64EG.Internal.p13ActualAttachmentColdFork,
        `Erdos64EG.Internal.p13ActualAttachmentColdFork_missing,
        `Erdos64EG.Internal.p13ActualAttachmentColdFork_same_selected_window,
        `Erdos64EG.Internal.p13ActualAttachmentColdFork_states_card_le_vertices,
        `Erdos64EG.Internal.p13ActualAttachmentColdForkCheckBudget,
        `Erdos64EG.Internal.p13ActualAttachmentColdForkCheckBudget_linear
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-structural-frontier"
      title := "Same-window P₁₃ structural frontier"
      summary := "From the exact node-[158] cold fork, the graph-owned degree, stub, deleted-edge-return, and first-event runners return exactly window surplus, a dyadic target hit, a corridor-high handoff, or a quiet ambient-finite structural germ."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowStructuralFrontier_exhaustive
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowStructuralFrontier,
        `Erdos64EG.Internal.routeSelectedWindowCorridor,
        `Erdos64EG.Internal.routeSelectedWindowCorridor_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
        `Erdos64EG.Internal.P13SameWindowStructuralFrontier.dyadic_target_same_stub,
        `Erdos64EG.Internal.P13SameWindowStructuralFrontier.high_handoff_same_stub,
        `Erdos64EG.Internal.P13SameWindowStructuralFrontier.dyadic_prefix_clear,
        `Erdos64EG.Internal.p13CorridorCertificateChecks,
        `Erdos64EG.Internal.p13CorridorCertificateChecks_le_vertices,
        `Erdos64EG.Internal.p13SameWindowStructuralVisibleChecks,
        `Erdos64EG.Internal.p13SameWindowStructuralVisibleChecks_eq
      ]
    },
    {
      stageId := "proof-slice.p13-node21-partxi-route"
      title := "Whole-packing same-context Part-XI route"
      summary := "Every exact node-[21] packed window retains its classifier-produced thirteen-bit cold residual and computed node-[159] frontier; the four structural subledgers partition exactly p13 windows without being identified with the open 91-coordinate response system."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.p13Node21PartXIRoutes_partition
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13Node21PartXIEntry,
        `Erdos64EG.Internal.p13Node21PartXIEntry,
        `Erdos64EG.Internal.p13Node21PartXIRoutes,
        `Erdos64EG.Internal.p13Node21PartXIRoutes_length,
        `Erdos64EG.Internal.P13Node21PartXIEntry.outcomeTag,
        `Erdos64EG.Internal.p13Node21PartXIRoutesWithTag
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-base-scale-split"
      title := "Quiet-germ D1--D3 base-scale split"
      summary := "Equality with the computed node-[159] quiet constructor permits one graph-owned support comparison at Qbase=4²·13²·2¹³, retaining exactly the literal short or strict long residual."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FixedTwoBoundaryCutState.state_card,
        `StructuralExhaustion.Graph.InducedPathColdGermScale.BoundedSameInterfaceResidual,
        `StructuralExhaustion.Graph.InducedPathColdGermScale.LongSupportResidual,
        `Erdos64EG.Internal.p13ColdD1D3BaseThreshold,
        `Erdos64EG.Internal.p13ColdD1D3BaseThreshold_eq_stateCard,
        `Erdos64EG.Internal.P13SameWindowQuietOutput,
        `Erdos64EG.Internal.P13SameWindowBaseScaleSplit,
        `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
        `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount,
        `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount_eq_one
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-short-third-incidence"
      title := "Short-return third-root incidence"
      summary := "Equality with node [161]'s computed short constructor fixes one bounded deleted-edge return; the graph root classifier selects its declared-order third incidence and returns exactly on-support or outside-boundary membership."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Setup,
        `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Setup.degree_eq_three,
        `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Result,
        `Erdos64EG.Internal.P13SameWindowComputedShort,
        `Erdos64EG.Internal.P13SameWindowComputedShort.root_degree_ge_three,
        `Erdos64EG.Internal.P13SameWindowComputedShort.root_mem_corridor,
        `Erdos64EG.Internal.P13SameWindowComputedShort.root_not_high,
        `Erdos64EG.Internal.P13SameWindowComputedShort.setup,
        `Erdos64EG.Internal.P13SameWindowComputedShort.return_support_bounded,
        `Erdos64EG.Internal.P13SameWindowShortThirdIncidence,
        `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
        `Erdos64EG.Internal.p13SameWindowShortThirdIncidence_visibleChecks_le
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-outside-boundary-star"
      title := "Outside-return cubic boundary-star ownership"
      summary := "Equality with node [162]'s computed outside constructor orients its one support-crossing incidence and packages the already cubic return root as a three-leaf star owning every root incidence."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.ownsAllRootIncidences
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.CubicStar.Data,
        `StructuralExhaustion.Graph.CubicStar.Data.SwitchBoundaryShape,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.OrientedReturnBoundary,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.additionalChecks_eq_zero,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.orientedBoundary,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.root_mem_return_support,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_outside_return_support,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_adjacent_root,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_ne_first_return,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_ne_restored_endpoint,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.cubicStar,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.switchBoundaryShape,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.additionalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-non-root-chord-resolution"
      title := "On-return chord resolution"
      summary := "Equality with node [162]'s computed on-support constructor locates the selected endpoint once; an accepted local chord closes through CT1, while the surviving residual is the exact strictly shorter deleted-edge return."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle_isCycle,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle_length,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.shorterReturn,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.shorterReturn_strict,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Result,
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.visibleChecks_le,
        `Erdos64EG.Internal.P13SameWindowComputedNonRootChord,
        `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.targetRun,
        `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.target_terminal,
        `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.target_impossible,
        `Erdos64EG.Internal.P13SameWindowShorterReturn,
        `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution_shorterExact,
        `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution_strict,
        `Erdos64EG.Internal.p13SameWindowNonRootChordResolution_visibleChecks_le
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-normalized-return-boundary"
      title := "Normalized one-return boundary rejoin"
      summary := "The exact node-[165] shorter-return and node-[166] outside-boundary computations rejoin into one branch-indexed return with an outside root incidence, cubic ownership, inherited Qbase bound, and strict-or-equal length evidence."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.RejectedChordRun,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.RejectedChordRun.firstNext_not_mem_shorter_support,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.selectedReturn,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.outsideVertex,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.cubicStar,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.DecreaseEvidence,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.NormalizedReturnBoundary,
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.additionalChecks_eq_zero,
        `Erdos64EG.Internal.P13SameWindowComputedShorterBoundary,
        `Erdos64EG.Internal.P13SameWindowComputedShorterBoundary.result_exact,
        `Erdos64EG.Internal.P13SameWindowNormalizedBoundaryInput,
        `Erdos64EG.Internal.P13SameWindowNormalizedReturnBoundary,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_support_bounded,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_length_le,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_outside,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_owns_root,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_rejected_strict,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_outside_length,
        `Erdos64EG.Internal.p13SameWindowNormalizedReturnBoundary_additionalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-packed-support-transition"
      title := "Normalized-return packed-support transition"
      summary := "One exact node-[167] return is scanned against the union of all ambient-cubic selected-window supports, yielding either full containment or the first membership transition with its exact boundary stub, outside endpoint, and induced-remainder component."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.Inside,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.TransitionAt,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.scan,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.support_subset_of_no_transition,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.ofFirstHit,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.windowPosition,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.outside_mem_externalNeighbors,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.boundaryStub,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Result,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks_eq,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks_le_square_add_linear,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.support_bounded,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.ambientPath,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.ambientPath_isPath,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.endpoint_mem_deletedWindowVertices,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput_path_length,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput_length_le_Qbase,
        `Erdos64EG.Internal.P13SameWindowNormalizedReturnPackedSupportTransition,
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
        `Erdos64EG.Internal.p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_eq,
        `Erdos64EG.Internal.p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_le
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-component-boundary-schedule"
      title := "Component boundary schedule and BFS path"
      summary := "The exact node-[168] first-transition stub is expanded by one computed deleted-edge return: a shared outside-component BFS supplies the first exit, an explicit first slot supplies a distinct second stub, the complete incident-stub list has a true cyclic successor, and declared-order BFS supplies a shortest component path."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.successor_distinct_and_same_returned_component
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.outsideBfsProfile,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentVertices,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.mem_componentVertices_iff,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.exitCertificate,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.windowPosition_firstHit,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.secondStub,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.second_distinct,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.incidentStubs,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.mem_incidentStubs_iff,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.two_le_incidentStubs_length,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.successor,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.successor_distinct,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.twoStubComponent,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath_isPath,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath_shortest,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.visibleChecks_eq,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.bfsBudget_polynomial,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.outsideBfsBudget_polynomial,
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.graphInput,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.result,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.anchor_is_exact_node168_stub,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.successor_distinct_and_same_returned_component,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.computed_exit_and_schedule,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.successor_is_stored_cyclic_next,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.slot_first_hit_provenance,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath_shortest,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.visibleChecks_eq,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.visibleChecks_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-component-d1d3-observation"
      title := "One component D1--D3 observation"
      summary := "The exact node-[170] two-boundary schedule is projected to one genuine State (Fin 0): two literal boundary degrees, two literal window offsets, and the independently computed declared-order BFS-tree shortest-path length. The empty local response explicitly retains MissingD4D7 reconstruction."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_missing_d4_d7
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.data,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.bfsPathTieBreak,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.canonicalPath,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.observations,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.emptyLocalProjection,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.state,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.OneStateResidual,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.run,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.boundaryDegree_zero,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.boundaryDegree_one,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.windowOffset_zero,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.windowOffset_one,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.targetResponse_eq,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.localResponse_empty,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.visibleChecks_eq,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.visibleChecks_linear,
        `Erdos64EG.Internal.P13SameWindowComponentD1D3Residual,
        `Erdos64EG.Internal.runP13SameWindowComponentD1D3Observation,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_exact_state,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_exact_node170_data,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_targetResponse,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_visibleChecks_eq,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_visibleChecks_linear
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-component-d1d3-ledger"
      title := "Cyclic component D1--D3 ledger split"
      summary := "The exact node-[173] residual supplies the retained anchor state. The complete node-[170] incident schedule is scanned in its stored cyclic order, producing either two observed rows with the same coarse D1--D3 state or a proof that the schedule has length at most Qbase."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD1D3Ledger
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Input,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.stubs,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.connector_successor_eq,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rowState,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rowState_anchor,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rows,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.stateCard,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Repetition,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Result,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.run,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.visibleChecks,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.localScale,
        `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowComponentD1D3LedgerSource,
        `Erdos64EG.Internal.computedP13SameWindowComponentD1D3LedgerSource,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.D1D3LedgerRepetition,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.D1D3LedgerOutput,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD1D3Ledger_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_exact_node170_schedule,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_source_exact_node173,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_true_cyclic_successor,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_anchor_row_eq_retained,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_retained_anchor_agrees_actual_node173,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_visibleChecks_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-component-d4d7-classifier"
      title := "D4--D7 availability and coarse-repeat routing"
      summary := "The exact node-[174] result is consumed on the same context. A coarse repeat is promoted through CT10 on its retained pair; a bounded schedule scans only its actual rows and returns a reconstructed family or the first typed missing D4--D7 row, with that residual routed through CT10."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7OrCoarseRepeat_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.run_exhaustive,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.visibleChecks_polynomial,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseExecution,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_terminal_promoted,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_trace_valid,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingExecution,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missing_trace_valid,
        `Erdos64EG.Internal.computedP13SameWindowComponentD4D7OrCoarseRepeatSource,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7OrCoarseRepeat,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_generic_node174,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_specialized_node174,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_totalVisibleChecks_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-component-d4d7-readiness"
      title := "Component D4--D7 semantic readiness"
      summary := "The exact node-[175] execution is inspected once. The impossible complete-reconstruction constructor is eliminated from the actual anchor row; the remaining coarse and bounded branches retain their exact CT10 routes and typed missing D4--D7 witnesses."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7SemanticReadiness_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.anchor_mem_stubs,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.reconstructed_impossible,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.run_exhaustive,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.visibleChecks_linear,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.computedD4D7SemanticReadinessSource,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7SemanticReadiness_exact_node175,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7SemanticReadiness,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7SemanticReadiness_visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7SemanticReadinessPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-packed-owner-change"
      title := "Ambient-cubic owner sequence and first cross-window edge"
      summary := "Equality with node [168]'s all-inside constructor prepares one stored unique ambient-cubic owner per return vertex; the impossible single-window branch is eliminated and the first owner change returns two exact cross-window tokens."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange_exact
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.OwnedSlot,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.OwnedSlot.window_unique,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.lookup,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.OwnerTable,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.prepareOwnerTable,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.OwnerChangeAt,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.FirstCrossWindow,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.FirstCrossWindow.ofFirstHit,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Result,
        `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.visibleChecks_le,
        `Erdos64EG.Internal.P13SameWindowComputedAllInside,
        `Erdos64EG.Internal.P13SameWindowComputedAllInside.graphInput_support_bounded,
        `Erdos64EG.Internal.P13SameWindowFirstCrossWindow,
        `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange,
        `Erdos64EG.Internal.p13SameWindowPackedOwnerChange_visibleChecks_le
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-cross-window-token-pair"
      title := "Exact cross-window token-pair residual"
      summary := "The exact node-[169] first owner-change edge is projected without a new search into a typed pair of distinct opposite oriented contributions of the same literal edge; both retained token subtypes remain exactly cross-window."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowCrossWindowTokenPair_source_exact
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.CrossWindowTokenPair,
        `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.route,
        `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.additionalChecks_eq_zero,
        `Erdos64EG.Internal.P13SameWindowCrossWindowTokenPair,
        `Erdos64EG.Internal.runP13SameWindowCrossWindowTokenPair,
        `Erdos64EG.Internal.p13SameWindowCrossWindowTokenPair_additionalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-long-support-prefix"
      title := "Exact long-support forced prefix"
      summary := "Equality with node [161]'s computed long constructor forces the first Qbase+1 literal support positions, their unique overflow index, and exact local prefix/after-prefix classifiers on the identical branch context."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClass_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.Source,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.Residual,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.prefixPositions_card,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.prefixEmbedding,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.overflowImage_val,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.classifyPrefixPosition,
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.classifyPosition,
        `Erdos64EG.Internal.P13SameWindowLongOutput,
        `Erdos64EG.Internal.p13SameWindowLongSource,
        `Erdos64EG.Internal.P13SameWindowLongSupportPrefix,
        `Erdos64EG.Internal.runP13SameWindowLongSupportPrefix,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_exact_length,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_exact_scale,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_card,
        `Erdos64EG.Internal.p13SameWindowLongSupportOverflowImage_val,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_overflow_iff,
        `Erdos64EG.Internal.p13SameWindowLongSupportPositionClass_exhaustive,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_ambient_preserved,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefixChecks,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefixChecks_eq_zero,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClassifierChecks,
        `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClassifierChecks_eq_one
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-long-prefix-state-labels"
      title := "First-nine observed-label refinement"
      summary := "The exact node-[163] source maps its first nine literal prefix positions to corridor vertices, computes only degree modulo four and selected-packing membership, retains an actual collision in the eight-label alphabet, and executes CT10 on exactly the two collided occurrences."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_terminal
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixObservedLabel.Input,
        `StructuralExhaustion.Graph.LongPrefixObservedLabel.labels_card,
        `StructuralExhaustion.Graph.LongPrefixObservedLabel.run,
        `StructuralExhaustion.Graph.LongPrefixObservedLabel.run_decision_exact,
        `StructuralExhaustion.Graph.LongPrefixObservedLabel.visibleChecks_le,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticCapability,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticInput_values,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_first_missing_responseContexts,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_trace,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_verified,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_trace_valid,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_total,
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticChecks_eq_nine,
        `Erdos64EG.Internal.P13SameWindowLongPrefixStateSource,
        `Erdos64EG.Internal.p13SameWindowLongPrefixStateSource,
        `Erdos64EG.Internal.p13SameWindowLongPrefixFirstNineEmbedding,
        `Erdos64EG.Internal.P13SameWindowLongPrefixStateLabels,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_distinct,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_sameCoarseLabel,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_trace,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_verified,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_trace_valid,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_total,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_totalVisibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-long-prefix-degree-refinement"
      title := "Two-occurrence exact degree refinement"
      summary := "The exact node-[164] collision and promoted CT10 response-context obligation are retained. Only the two literal corridor degree rows are read, yielding equal full degrees or a nonzero degree gap with the same residue modulo four."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.run,
        `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.source_occurrences_distinct,
        `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.visibleChecks_le,
        `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_node164,
        `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_ct10_run,
        `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_ct10_promotion_responseContexts,
        `Erdos64EG.Internal.p13SameWindowLongPrefixDegree_firstVertex_exact,
        `Erdos64EG.Internal.p13SameWindowLongPrefixDegree_secondVertex_exact,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_distinct,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.p13-same-window-dyadic-terminal"
      title := "Computed dyadic frontier branch closes"
      summary := "The dyadic constructor of node [159] is converted, without a fresh witness, to the exact cold dyadic hit; the established one-check CT1 G1 run reaches C1 and contradicts target avoidance."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.P13ComputedDyadicBranch.impossible
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13ComputedDyadicBranch,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit_offset,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.stub_window,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit_cycle_eq_rootCycle,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.g1Run,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_terminal,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_trace,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_checks,
        `Erdos64EG.P13ColdGermTerminalRoutes.g1Run,
        `Erdos64EG.P13ColdGermTerminalRoutes.g1_impossible
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-rank"
      title := "Exact remainder curvature CT15"
      summary := "The exact node-[28] remainder is scanned for boundary incidences and raw length-two wedges; CT15 evaluates the literal wedge supports and certified-reduction admissibility forces its full-rank ledger."
      kind := .tactic
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedP13CurvaturePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.positiveDeficiency_le_boundaryIncidences,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeFloor,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeCount_le_cube,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le,
        `Erdos64EG.Internal.p13CurvatureCoordinates,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_eq_wedgeCount,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_le_cube,
        `Erdos64EG.Internal.p13CurvatureResponseProfile,
        `StructuralExhaustion.Graph.FiniteSupportResponse.Profile.run,
        `Erdos64EG.Internal.runP13CurvatureCT15_terminal,
        `Erdos64EG.Internal.runP13CurvatureCT15_trace,
        `Erdos64EG.Internal.no_p13Curvature_rankDrop,
        `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix,
        `Erdos64EG.Internal.exists_verifiedP13CurvaturePrefix
      ]
    },
    {
      stageId := "proof-slice.proper-delocalization"
      title := "Proper enlarged-support closure"
      summary := "The enlarged determination support is tagged as proper or whole-graph. A proper support is audited by literal context response and the existing CT3 compression kernel; only the unchanged whole-graph payload survives."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.verifiedStage,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.targetDefective,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.compression_terminal,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.compression_trace,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.Location,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.route,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.routeAfterRankDrop,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.verifiedStage,
        `Erdos64EG.Internal.routeProperDelocalization,
        `Erdos64EG.Internal.routeRankDropThroughProperDelocalization,
        `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix
      ]
    },
    {
      stageId := "proof-slice.global-rank-drop-closure"
      title := "Whole-support rank-drop audit"
      summary := "The exact whole payload carries the quotient already admitted by the finite determination certificate. Minimality makes that quotient injective, so its literal distinct-coordinate identification closes; the one--three identity is derived separately from one finite graph component."
      kind := .tactic
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedP13GlobalRankClosurePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.injective,
        `StructuralExhaustion.Graph.ClosedRankDrop.exactBarrier,
        `StructuralExhaustion.Graph.ClosedRankDrop.no_silent_identification,
        `StructuralExhaustion.Graph.ClosedRankDrop.rankDrop_impossible,
        `StructuralExhaustion.Core.OneThreeRepair.identity,
        `StructuralExhaustion.Graph.OneThreeRepair.Component.identity,
        `Erdos64EG.Internal.P13WholeDelocalization,
        `Erdos64EG.Internal.routeRankDropThroughGlobalClosure,
        `Erdos64EG.Internal.p13ClosedRankDrop_exactBarrier,
        `Erdos64EG.Internal.no_p13Closed_silentIdentification,
        `Erdos64EG.Internal.p13WholeDelocalization_impossible,
        `Erdos64EG.Internal.oneThreeRepair_identity,
        `Erdos64EG.Internal.oneThreeRepair_component_identity,
        `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix,
        `Erdos64EG.Internal.exists_verifiedP13GlobalRankClosurePrefix
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
      stageId := "proof-slice.degree-four-type-b-ledger"
      title := "CT14 degree-four Type B fan ledger"
      summary := "On the no-higher-centre branch, every actual centre has degree exactly four; CT14 computes its exact closed-port count, quarter-deficit, and assigned-certificate split."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedDegreeFourTypeBLedgerPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.DegreeFourFanLedger.members_card_eq_degree,
        `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedStage,
        `StructuralExhaustion.Graph.FiniteCertificateMarking.Profile.marked_or_residual,
        `Erdos64EG.Internal.TypeBSupportScope.degree_eq_four_of_noHigher,
        `Erdos64EG.Internal.TypeBSupportScope.higher_or_degreeFour_certificateFlow
      ]
    },
    {
      stageId := "proof-slice.degree-four-b2-routing"
      title := "Exact degree-four B1/B2 routing"
      summary := "The node-[80] assigned certificate is now a required provenance field of every local entry. Finite resolution plus CT12 returns an unresolved center, a nonnegative full choice, a literal remaining negative core, or a proof-carrying minimal overlap."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedDegreeFourB2RoutingPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBSupportScope.unresolved_of_certificate_none,
        `Erdos64EG.Internal.TypeBSupportScope.certificateResidual_is_unresolved,
        `Erdos64EG.Internal.TypeBSupportScope.fullResolution_entry_provenance,
        `Erdos64EG.Internal.TypeBSupportScope.degreeFourB2Route,
        `Erdos64EG.Internal.TypeBSupportScope.fullChoice_nonnegative_or_remainingNegative,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_disjoint_choice,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_subschedule_has_choice,
        `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_separated_carrier_partition
      ]
    },
    {
      stageId := "proof-slice.type-b-residual-center-ledger"
      title := "Assigned-surplus residual-center ledger"
      summary := "Every certificate failure, unresolved local entry, and selected center of a minimal B2 overlap is an actual high center in the same scope and is bounded by its graph-derived assigned-surplus sum."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedTypeBResidualCenterLedgerPrefix
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBSupportScope.residualCenters_card_le_assignedSurplus,
        `Erdos64EG.Internal.TypeBSupportScope.certificateResidual_charged,
        `Erdos64EG.Internal.TypeBSupportScope.unresolved_charged,
        `Erdos64EG.Internal.TypeBSupportScope.minimalOverlapCenters_charged,
        `Erdos64EG.Internal.TypeBSupportScope.minimalOverlap_has_assignedSurplus
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
        `Erdos64EG.Internal.exists_verifiedSparseSurplusPrefix,
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
        `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure,
        `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure_sameLabelPrefix
      ]
    },
    {
      stageId := "proof-slice.baseline-spine-demand"
      title := "CT15 baseline-spine demand"
      summary := "The sparse-envelope output first activates every exact CT6 surplus slot through its CT2-derived return and open-suppression or triangular response. The exact cubic-baseline skeleton count and integer bit budget are then computed from n; CT15 certifies the canonical baseline-demand ledger. No linear deficit estimate is assumed."
      kind := .tactic
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedBaselineSpineDemandPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivation.verifiedActivatedStageFromMinimality,
        `StructuralExhaustion.Graph.SurplusPortActivation.activatedSchedule_length_eq_residualTotal,
        `Erdos64EG.Internal.surplusPortActivationSetup,
        `Erdos64EG.Internal.activatedSurplusStage,
        `Erdos64EG.Internal.activeSurplusDemand,
        `Erdos64EG.Internal.activatedSurplusSchedule_length_eq_sigma,
        `Erdos64EG.Internal.openResponse_has_mersenne_length,
        `Erdos64EG.Internal.verifiedSurplusPortActivationPrefix,
        `Erdos64EG.Internal.exists_verifiedSurplusPortActivationPrefix,
        `StructuralExhaustion.CT15.BaselineDemand.Profile.verifiedStage,
        `StructuralExhaustion.CT15.run_terminal_eq_fullRankLedger_of_noDrop_of_total_le_capacity,
        `StructuralExhaustion.CT15.ledgerTotal_eq_card_of_charge_eq_one,
        `StructuralExhaustion.CT15.linearCheckBudget,
        `Erdos64EG.Internal.baselineSpineEdgeSlots,
        `Erdos64EG.Internal.baselineSpineEdgeCount,
        `Erdos64EG.Internal.baselineSpineStateCount,
        `Erdos64EG.Internal.baselineSpineBitBudget,
        `Erdos64EG.Internal.baselineSpineProfile,
        `Erdos64EG.Internal.baselineSpineProfile_coordinateCount,
        `Erdos64EG.Internal.baselineSpineProfile_exactDeficit,
        `Erdos64EG.Internal.baselineSpineProfile_lowerBound,
        `Erdos64EG.Internal.runBaselineSpineCT15_terminal,
        `Erdos64EG.Internal.runBaselineSpineCT15_trace,
        `Erdos64EG.Internal.runBaselineSpineCT15_verified,
        `Erdos64EG.Internal.runBaselineSpineCT15_total,
        `Erdos64EG.Internal.runBaselineSpineCT15_linearBudget
      ]
    },
    {
      stageId := "proof-slice.sparse-pair-responses"
      title := "CT15 exact free/blocked pair responses"
      summary := "The exact activated-slot schedule is paired once, each pair is classified by a finite local blocker scan, and every free pair receives one proof-carrying shortest connector. CT15 then verifies full rank under the audited admissible-quotient contract; boundary and target mismatches are raw-proposal exits and cannot occur after admission."
      kind := .tactic
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteBlockerLedger.FamilyProfile.blocked_card_add_free_card,
        `StructuralExhaustion.Core.FiniteBlockerLedger.FamilyProfile.firstBlocker_sound,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.preconnected_of_noProperCore,
        `StructuralExhaustion.Graph.FiniteConnector.exists_certificate,
        `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.no_boundary_mismatch,
        `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.no_target_mismatch,
        `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.injective,
        `StructuralExhaustion.CT15.AdmissibleQuotient.Profile.verifiedFor,
        `StructuralExhaustion.Graph.SurplusPairResponse.verifiedStage,
        `StructuralExhaustion.Graph.SurplusPairResponse.canonicalBlocker_sound,
        `Erdos64EG.Internal.sparsePair_exact_partition,
        `Erdos64EG.Internal.sparsePairCT15_verified,
        `Erdos64EG.Internal.sparsePair_schedule_quartic,
        `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix
      ]
    },
    {
      stageId := "proof-slice.total-pair-token-route"
      title := "CT9 pair dispatch and free-anchor route"
      summary := "CT9 executes the exact node-130 pre-retokenization dispatch by first selected port and a five-way role. Blocked pairs retain their canonical first-hit record for node 134; blocker-free pairs receive the literal freeAnchor role and enter the primitive selected-port audit with their retained shortest connector. The downstream capacity-token map is not part of this stage."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.CT9.TokenRoleLedger.noOvercounting,
        `StructuralExhaustion.CT9.TokenRoleLedger.bounded_total,
        `StructuralExhaustion.CT9.TokenRoleLedger.verifiedStage,
        `StructuralExhaustion.Graph.SurplusTokenRole.pairRouteRole_card,
        `StructuralExhaustion.Graph.SurplusTokenRole.totalRole_card,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.free_role,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.blocked_role,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.freeAnchorFibre_member_is_free,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.freeAnchorFibre_member_first,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.blocked_retains_canonical_blocker,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_verified,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_traceValid,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_total,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.checks_le_five_mul_sixthPower,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.checks_le_five_mul_cube_of_token_card_le,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.verifiedStage,
        `Erdos64EG.Internal.allPairTokenRouting_terminal,
        `Erdos64EG.Internal.allPairTokenRouting_verified,
        `Erdos64EG.Internal.allPairTokenRouting_traceValid,
        `Erdos64EG.Internal.allPairTokenRouting_total,
        `Erdos64EG.Internal.allPairTokenRouting_noOvercounting,
        `Erdos64EG.Internal.allPairTokenRouting_freeHandoff,
        `Erdos64EG.Internal.allPairTokenRouting_blockedHandoff,
        `Erdos64EG.Internal.allPairTokenRouting_checks,
        `Erdos64EG.Internal.allPairTokenRouting_checks_polynomial,
        `Erdos64EG.Internal.allPairTokenRouting_tokenCount_le_vertexCount,
        `Erdos64EG.Internal.allPairTokenRouting_checks_cubic,
        `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix
      ]
    },
    {
      stageId := "proof-slice.capacity-token-ledger"
      title := "CT9 capacity-token and exact join ledger"
      summary := "The exact blocked output is retokenized by the manuscript priority map; the selected induced-P13 packing supplies the window-join identity; the existing free-anchor side and the blocked side form one exact 25-role partition of every scheduled pair."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathWindowLedger.tokens_card_eq_fifteen_mul_packing_add_surplus,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.input_items_eq_source,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.free_token,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.blocked_token,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.noOvercounting,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.token_supply_exact,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.verifiedStage,
        `Erdos64EG.Internal.sparsePairAuditExit_closed,
        `Erdos64EG.Internal.canonicalBlockedToken_total,
        `Erdos64EG.Internal.exactWindowJoinIdentity,
        `Erdos64EG.Internal.capacityTokenSupply_exact,
        `Erdos64EG.Internal.totalCapacityLedger_noOvercounting,
        `Erdos64EG.Internal.totalCapacityRoleCount,
        `Erdos64EG.Internal.capacityLedgerChecks_cubic,
        `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix
      ]
    },
    {
      stageId := "proof-slice.coupled-class-overload"
      title := "CT9 exact coupled class overload"
      summary := "For every fixed threshold triple, CT9 compares the literal complete surplus-pair count with the exact 25-role class capacity. Positive excess returns an actual overloaded fibre and its token-class route; the other side proves the explicit quadratic surplus bound."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.exactPartition,
        `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.decide,
        `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.totalCapacity_le,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.exactPartition,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.routeClass,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.routedOverload,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.totalCapacity_le,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.verifiedStage,
        `Erdos64EG.Internal.coupledClassProfile,
        `Erdos64EG.Internal.coupledExcess_positive_iff,
        `Erdos64EG.Internal.coupledOverloadClassRoute,
        `Erdos64EG.Internal.coupledPairCount_eq_chooseSurplus,
        `Erdos64EG.Internal.withinCoupledCapacity_pairBound,
        `Erdos64EG.Internal.noCoupledOverload_quadraticSpine,
        `Erdos64EG.Internal.coupledClassChecks_cubic,
        `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix
      ]
    },
    {
      stageId := "proof-slice.homogeneous-pattern"
      title := "Greedy homogeneous matching--star audit"
      summary := "The graph layer projects CT9's actual overloaded token--role fibre, follows its literal window/remainder/primitive class route, and performs one deterministic greedy maximal-matching scan. The sharp local cap yields the corresponding matching or star without searching a pattern family."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedHomogeneousPatternPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.GreedyMatchingStar.greedy,
        `StructuralExhaustion.Core.GreedyMatchingStar.greedy_pairwise,
        `StructuralExhaustion.Core.GreedyMatchingStar.greedy_covers,
        `StructuralExhaustion.Core.GreedyMatchingStar.exists_pattern_of_cap_lt_card,
        `StructuralExhaustion.Graph.SurplusHomogeneousPattern.audit,
        `Erdos64EG.Internal.homogeneousPatternAudit,
        `Erdos64EG.Internal.exists_verifiedHomogeneousPatternPrefix
      ]
    },
    {
      stageId := "proof-slice.type-b-local-fan-mass"
      title := "CT14 local selected-center fan mass"
      summary := "The exact node-[75]/[81]--[83] local scope is scanned directly; every literal selected high center contributes unit lower mass paid by its own degree surplus."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedTypeBLocalFanMassPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedStage,
        `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.selectedCount_le_totalSurplus,
        `Erdos64EG.Internal.TypeBSupportScope.localFanMass,
        `Erdos64EG.Internal.TypeBSupportScope.overlapCenters_card_eq_selected_length,
        `Erdos64EG.Internal.TypeBSupportScope.localFanMassRoute,
        `Erdos64EG.Internal.exists_verifiedTypeBLocalFanMassPrefix
      ]
    },
    {
      stageId := "proof-slice.coarse-bottleneck-classification"
      title := "Fixed coarse bottleneck classification"
      summary := "The exact 49-pair predecessor pattern is scanned against 48 structural codes; the first actual collision, its maps, two rooted germs, and typed semantic trigger are retained."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedGeometricBottleneckClassificationPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.verifiedCollision,
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.toSemanticBottleneckTrigger,
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_total,
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_source_exact,
        `Erdos64EG.Internal.coarseBottleneckClassification,
        `Erdos64EG.Internal.geometricCollisionChecks_eq,
        `Erdos64EG.Internal.geometricClassificationWork_eq,
        `Erdos64EG.Internal.exists_verifiedGeometricBottleneckClassificationPrefix
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-classification"
      title := "Finite attachment and germ-shape classification"
      summary := "The exact node-[144] trigger is scanned on its retained 78p attachment coordinates. The first map mismatch is returned, or full alignment is proved and the stored rooted-germ comparison is classified into one of four exact shapes."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckClassificationPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FinitePredicateAlignment.Profile.decide,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify_source_exact,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify_total,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run_verified,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run_trace_valid,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classificationWork_le_vertices,
        `Erdos64EG.Internal.semanticBottleneckClassification,
        `Erdos64EG.Internal.semanticBottleneck_source_exact,
        `Erdos64EG.Internal.semanticBottleneck_ct10_verified,
        `Erdos64EG.Internal.semanticBottleneckClassificationWork_le_vertices,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckClassificationPrefix
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-local-consumer"
      title := "Local semantic-bottleneck separator split"
      summary := "All five exact node-[177] leaves are consumed. Mismatch and prefix leaves are retained verbatim; root and after-edge divergences expose literal distinct incidences and split only on the locally read separator degree."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalConsumerPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.classify,
        `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.classify_total,
        `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.checks_le_linear,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_previous_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_frontier_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_total,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_checks_le_vertices,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalConsumerPrefix
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-switch-normalization"
      title := "Cubic switch normalization"
      summary := "The exact node-[178] frontier is normalized without new checks: mismatch and prefix leaves are unchanged, cubic divergence leaves become literal four-vertex cubic-star data, and high leaves retain only degree at least four."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckSwitchNormalizationPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.normalize,
        `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.normalize_total,
        `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.checks_eq_zero,
        `Erdos64EG.Internal.semanticBottleneckNormalizationSource_node178_exact,
        `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_result_exact,
        `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_total,
        `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_checks_eq_zero,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckSwitchNormalizationPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-component-d4d7-clause-schedule"
      title := "Fixed D4--D7 clause schedule"
      summary := "The exact node-[180] markers are retained and assigned the fixed noduplicated D4,D5,D6,D7 obligation order. Coarse output has two ledgers and bounded output one; no clause truth is asserted."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseSchedulePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.clauseOrder_nodup,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.run_total,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.emittedSlots_le_eight,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseSchedule_exact_node180,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseSchedule_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseSchedule_emittedSlots_le_eight,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseSchedulePrefix
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-local-clause-alignment"
      title := "First-nine local-clause alignment"
      summary := "The exact node-[179] result and CT10 response-context obligation are retained. Adjacency of the two literal vertices is compared on the same nine prefix coordinates, producing the first mismatch or alignment on exactly those nine clauses."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.run,
        `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.visibleChecks_constant,
        `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.exact_node179,
        `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-local-projection"
      title := "Local separator projection"
      summary := "The exact node-[181] leaves are projected to literal cubic switch-boundary data or the identical high-center port row; mismatch and prefix leaves are unchanged."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalProjectionPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.project,
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.project_total,
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.visibleChecks_linear,
        `Erdos64EG.Internal.semanticBottleneckLocalProjectionSource_node181_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_projection_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_total,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_visibleChecks_linear,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalProjectionPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-component-d4d7-clause-cursor"
      title := "D4 obligation cursor"
      summary := "The exact node-[182] ledgers retain their dependent markers, focus D4 as the next obligation, and preserve the exact D5,D6,D7 tail without asserting truth."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseCursorPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.run_total,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.remainingSlots_le_six,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseCursor_exact_node182,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseCursor_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseCursor_remainingSlots_le_six,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseCursorPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-extended-clause-alignment"
      title := "First-eighteen local-clause alignment"
      summary := "An inherited first-nine mismatch passes through; otherwise only literal positions 9 through 17 are scanned, yielding a second-block mismatch or alignment on the first eighteen coordinates."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.run,
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.exact_node183,
        `Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-strong-frontier"
      title := "Strong-semantic obligation frontier"
      summary := "Every exact node-[184] leaf is retained and tagged with its next pending obligation. The tags are requests, not sparse-exit, CT3, Type B, or fixed-cap certificates."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckStrongFrontierPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify,
        `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_total,
        `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_retains,
        `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_obligation_exact,
        `Erdos64EG.Internal.semanticBottleneckStrongFrontierSource_node184_exact,
        `Erdos64EG.Internal.semanticBottleneckStrongFrontier_pending_exact,
        `Erdos64EG.Internal.semanticBottleneckStrongFrontier_retains_node184,
        `Erdos64EG.Internal.semanticBottleneckStrongFrontier_total,
        `Erdos64EG.Internal.semanticBottleneckStrongFrontier_visibleChecks_constant,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckStrongFrontierPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-component-d4-local-clause-request"
      title := "Graph-derived D4 evaluation request"
      summary := "The exact node-[185] cursors emit one singleton D4 request per actual marker while retaining the dependent marker and literal D5,D6,D7 tail. No truth value is supplied."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4LocalClauseRequestPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.request,
        `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.run_total,
        `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.requestedSlots_le_two,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4LocalClauseRequest_exact_node185,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4LocalClauseRequest_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4LocalClauseRequest_requestedSlots_le_two,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4LocalClauseRequestPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-third-block-clause-alignment"
      title := "First-twenty-seven local-clause alignment"
      summary := "Earlier mismatches pass through unchanged; after first-eighteen alignment only literal positions 18 through 26 are scanned, producing a third mismatch or exact first-twenty-seven alignment."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.run,
        `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.source_extended_exact,
        `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.exact_node186,
        `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.retained_degree_result,
        `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-first-clause"
      title := "First local separator clause"
      summary := "Node [190] retains the exact node-[187] payload and tag. Cubic leaves expose their three boundary incidences and high leaves their first four distinct declared ports; no requested semantic certificate is claimed."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckFirstClausePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.certify,
        `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.run,
        `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.run_total,
        `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.visibleChecks_constant,
        `Erdos64EG.Internal.semanticBottleneckFirstClauseSource_node187_exact,
        `Erdos64EG.Internal.semanticBottleneckFirstClause_result_exact,
        `Erdos64EG.Internal.semanticBottleneckFirstClause_obligation_exact,
        `Erdos64EG.Internal.semanticBottleneckFirstClause_total,
        `Erdos64EG.Internal.semanticBottleneckFirstClause_visibleChecks_constant,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckFirstClausePrefix
      ]
    },
    {
      stageId := "proof-slice.p13-component-d4-evaluator-residual"
      title := "D4 evaluator residual"
      summary := "Each exact node-[188] request retains its dependent marker and D5--D7 tail and exposes exactly the missing graph-local predicate and provenance requirements. No evaluator or Boolean is accepted."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorResidualPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.residual,
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.run_total,
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.requiredInputs_le_four,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4EvaluatorResidual_exact_node188,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorResidual_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorResidual_requiredInputs_le_four,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorResidualPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      title := "First-thirty-six local-clause alignment"
      summary := "All inherited mismatch leaves pass through unchanged; only literal positions 27 through 35 are scanned after first-twenty-seven alignment."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.run,
        `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.source_third_exact,
        `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.exact_node189,
        `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.retained_degree_result,
        `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_ambient_preserved
      ]
    },
    {
      stageId := "proof-slice.semantic-bottleneck-pairwise-clause"
      title := "Pairwise local separator clause"
      summary := "The exact node-[190] certificate yields only pairwise boundary or endpoint inequalities and retains the pending semantic obligation unchanged. This is the manuscript-boundary residual interface."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.exists_verifiedSemanticBottleneckPairwiseClausePrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LocalSeparatorPairwiseClause.cubic,
        `StructuralExhaustion.Graph.LocalSeparatorPairwiseClause.high,
        `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.run,
        `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.run_total,
        `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.visibleChecks_eq_zero,
        `Erdos64EG.Internal.semanticBottleneckPairwiseClauseSource_node190_exact,
        `Erdos64EG.Internal.semanticBottleneckPairwiseClause_result_exact,
        `Erdos64EG.Internal.semanticBottleneckPairwiseClause_obligation_exact,
        `Erdos64EG.Internal.semanticBottleneckPairwiseClause_total,
        `Erdos64EG.Internal.semanticBottleneckPairwiseClause_visibleChecks_eq_zero,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckPairwiseClausePrefix
      ]
    },
    {
      stageId := "proof-slice.p13-component-d4-evaluator-construction-residual"
      title := "Graph-owned D4 evaluator construction residual"
      summary := "The exact node-[191] requests retain their markers and D5--D7 tails and are refined into the three graph-owned construction requirements. No predicate, evaluator, or Boolean is supplied."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorConstructionPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual.residual,
        `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual.constructionInputs,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorConstruction_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorConstruction_requiredInputs_le_six,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorConstructionPrefix
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-compatible-response-frontier"
      title := "Long-prefix compatible-response frontier"
      summary := "The exact five node-[192] leaves are retained. Mismatch leaves expose two requirements and the aligned leaf exposes three graph-owned response/provenance/CT8 requirements without claiming compatible-response semantics."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_predecessor,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.requiredInputs_le_three,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.visibleChecks_constant,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_degree_result,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_requiredInputs,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_ambient_preserved
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
      linkId := "proof-slice.p13-labels-surplus-scale"
      sourceStageId := "proof-slice.p13-labels"
      targetStageId := "proof-slice.surplus-scale-split"
      kind := .frameworkComposition
      label := "exact node-[18] surplus handoff"
      description := "The same selected graph supplies its literal total degree surplus and order to the constant-work squared-scale comparison. The three homogeneous thresholds remain explicit authored local data."
      automationDeclarations := [
        `StructuralExhaustion.Core.QuadraticScaleSplit.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedP13LabelAlgebraPrefix,
        `Erdos64EG.Internal.exists_verifiedSurplusScaleSplitPrefix
      ]
    },
    {
      linkId := "proof-slice.p13-packing-positive-deficiency"
      sourceStageId := "proof-slice.p13-packing"
      targetStageId := "proof-slice.p13-positive-deficiency"
      kind := .frameworkComposition
      label := "exact remainder support"
      description := "The graph charge profile takes the literal CT12 remainder finset and computes induced degrees and positive deficiency on it without selecting another graph or support."
      automationDeclarations := [
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.positiveDeficiency
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedP13PackingPrefix,
        `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix
      ]
    },
    {
      linkId := "proof-slice.surplus-scale-multiscale-curvature"
      sourceStageId := "proof-slice.surplus-scale-split"
      targetStageId := "proof-slice.p13-multiscale-curvature"
      kind := .frameworkComposition
      label := "exact bounded constructor"
      description := "The combined router preserves the strict sparse-pressure residual unchanged and discharges only the bounded constructor with the complete CT10 curvature certificate."
      evidenceDeclarations := [
        `Erdos64EG.Internal.routeSurplusScale,
        `Erdos64EG.Internal.routeSurplusScaleThroughCurvature,
        `Erdos64EG.Internal.routeSurplusScaleThroughCurvature_exhaustive
      ]
    },
    {
      linkId := "proof-slice.p13-multiscale-node21-partxi-route"
      sourceStageId := "proof-slice.p13-multiscale-curvature"
      targetStageId := "proof-slice.p13-node21-partxi-route"
      kind := .frameworkComposition
      label := "retain the exact node-[21] prefix"
      description := "The Part-XI route is indexed by the identical VerifiedP13MultiScaleCurvaturePrefix. It maps the graph-owned CT12 packing once and stores the computed actual-attachment fork and structural frontier for every selected window; it does not claim the open 91-coordinate realization branch."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node21PartXIEntry,
        `Erdos64EG.Internal.p13Node21PartXIRoutes,
        `Erdos64EG.Internal.p13Node21PartXIRoutes_partition
      ]
    },
    {
      linkId := "proof-slice.p13-multiscale-actual-attachment-cold-fork"
      sourceStageId := "proof-slice.p13-multiscale-curvature"
      targetStageId := "proof-slice.p13-actual-attachment-cold-fork"
      kind := .frameworkComposition
      label := "pointwise actual selected-window scan"
      description := "The exact node-[21] predecessor and selected-window provenance are retained while the graph-owned actual thirteen-bit classifier is run. This route is separate from the still-open 91-coordinate realization branch."
      automationDeclarations := [
        `StructuralExhaustion.Core.LocalBooleanRealization.System.classify
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13MultiScaleCurvaturePrefix,
        `Erdos64EG.Internal.p13ActualAttachmentColdFork
      ]
    },
    {
      linkId := "proof-slice.p13-actual-cold-same-window-frontier"
      sourceStageId := "proof-slice.p13-actual-attachment-cold-fork"
      targetStageId := "proof-slice.p13-same-window-structural-frontier"
      kind := .frameworkComposition
      label := "same selected window, graph-owned corridor"
      description := "The exact node-[158] cold-fork value indexes the result. The framework first classifies the thirteen actual degrees, then selects the canonical cubic stub when appropriate and scans only its proof-carrying deleted-edge return."
      automationDeclarations := [
        `StructuralExhaustion.Graph.InducedPathColdStubSelection.classify,
        `StructuralExhaustion.Graph.InducedPathColdCorridor.runFirstFailure
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13ActualAttachmentColdFork,
        `Erdos64EG.Internal.routeSelectedWindowCorridor,
        `Erdos64EG.Internal.runP13SameWindowStructuralFrontier
      ]
    },
    {
      linkId := "proof-slice.p13-same-window-frontier-base-scale-split"
      sourceStageId := "proof-slice.p13-same-window-structural-frontier"
      targetStageId := "proof-slice.p13-same-window-base-scale-split"
      kind := .frameworkComposition
      label := "computed quiet constructor"
      description := "The input retains equality with node [159]'s computed quiet constructor, including the exact fork, selected window, canonical stub, no-event proof, and structural germ. The framework performs only the support-length comparison."
      automationDeclarations := [
        `StructuralExhaustion.Graph.InducedPathColdGermScale.route
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
        `Erdos64EG.Internal.P13SameWindowQuietOutput
      ]
    },
    {
      linkId := "proof-slice.p13-base-scale-short-third-incidence"
      sourceStageId := "proof-slice.p13-same-window-base-scale-split"
      targetStageId := "proof-slice.p13-same-window-short-third-incidence"
      kind := .frameworkComposition
      label := "computed short constructor"
      description := "The input records equality with node [161]'s computed short result. The baseline and quiet germ make the exact return root cubic; the graph runner selects only its third declared incidence and tests that endpoint against the retained bounded support."
      automationDeclarations := [
        `StructuralExhaustion.Graph.RootIncidence.classify,
        `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.run
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
        `Erdos64EG.Internal.P13SameWindowComputedShort
      ]
    },
    {
      linkId := "proof-slice.p13-short-third-incidence-outside-boundary-star"
      sourceStageId := "proof-slice.p13-same-window-short-third-incidence"
      targetStageId := "proof-slice.p13-same-window-outside-boundary-star"
      kind := .frameworkComposition
      label := "computed outside constructor"
      description := "The input records equality with node [162]'s exact outside result. The reusable graph layer retains that same support crossing, packages the already certified cubic root, and proves its three displayed leaves own all root incidences."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.orientedBoundary,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.cubicStar,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.switchBoundaryShape,
        `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.ownsAllRootIncidences
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.graphBranch
      ]
    },
    {
      linkId := "proof-slice.p13-short-third-incidence-non-root-chord-resolution"
      sourceStageId := "proof-slice.p13-same-window-short-third-incidence"
      targetStageId := "proof-slice.p13-same-window-non-root-chord-resolution"
      kind := .frameworkComposition
      label := "computed on-support constructor"
      description := "The input records equality with node [162]'s exact on-support result. The graph resolver scans only that supplied short support, constructs its literal chord, and otherwise returns the exact shorter deleted-edge return."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.run
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
        `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.genericInput
      ]
    },
    {
      linkId := "proof-slice.p13-chord-resolution-normalized-return-boundary"
      sourceStageId := "proof-slice.p13-same-window-non-root-chord-resolution"
      targetStageId := "proof-slice.p13-same-window-normalized-return-boundary"
      kind := .frameworkComposition
      label := "exact rejected-chord shorter return"
      description := "The branch input retains equality with node [165]'s actual runner and its exact strictly shorter return. The graph normalizer chooses that return and the old first step as its outside incidence."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.normalize
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution,
        `Erdos64EG.Internal.P13SameWindowNormalizedBoundaryInput.graphInput
      ]
    },
    {
      linkId := "proof-slice.p13-outside-boundary-star-normalized-return-boundary"
      sourceStageId := "proof-slice.p13-same-window-outside-boundary-star"
      targetStageId := "proof-slice.p13-same-window-normalized-return-boundary"
      kind := .frameworkComposition
      label := "exact outside-boundary cubic star"
      description := "The branch input retains equality with node [166]'s computed outside result. The graph normalizer keeps the original return, selected outside endpoint, and the same cubic root ownership."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.normalize
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.graphBranch,
        `Erdos64EG.Internal.P13SameWindowNormalizedBoundaryInput.graphInput
      ]
    },
    {
      linkId := "proof-slice.p13-normalized-return-packed-support-transition"
      sourceStageId := "proof-slice.p13-same-window-normalized-return-boundary"
      targetStageId := "proof-slice.p13-same-window-packed-support-transition"
      kind := .frameworkComposition
      label := "exact computed normalized return"
      description := "The input stores equality with node [167]'s actual normalized result. Its return is viewed in the ambient graph, and its selected-window endpoint is proved to lie in the union of all ambient-cubic selected-window supports before the one-path transition scan."
      automationDeclarations := [
        `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.run
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary,
        `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput
      ]
    },
    {
      linkId := "proof-slice.p13-packed-support-transition-component-boundary-schedule"
      sourceStageId := "proof-slice.p13-same-window-packed-support-transition"
      targetStageId := "proof-slice.p13-same-window-component-boundary-schedule"
      kind := .frameworkComposition
      label := "exact first-transition constructor"
      description := "The input retains equality with node [168]'s actual first-transition result and its exact stub, endpoint, and returned component. The graph layer uses that same computed outside BFS component for the exit scan, incident schedule, second stub, and shortest component path."
      automationDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.exitCertificate
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.anchor_is_exact_node168_stub,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.computed_exit_and_schedule
      ]
    },
    {
      linkId := "proof-slice.p13-component-boundary-schedule-component-d1d3-observation"
      sourceStageId := "proof-slice.p13-same-window-component-boundary-schedule"
      targetStageId := "proof-slice.p13-same-window-component-d1d3-observation"
      kind := .frameworkComposition
      label := "exact computed two-boundary schedule"
      description := "The consumer receives node [170]'s actual graph input and result. It independently runs the declared-order BFS tree on that computed component, then packages equality to that one computed shortest path as a rank; it does not order or scan a path family."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.result,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath_shortest,
        `Erdos64EG.Internal.p13SameWindowComponentD1D3_exact_node170_data
      ]
    },
    {
      linkId := "proof-slice.p13-component-d1d3-observation-ledger"
      sourceStageId := "proof-slice.p13-same-window-component-d1d3-observation"
      targetStageId := "proof-slice.p13-same-window-component-d1d3-ledger"
      kind := .frameworkComposition
      label := "retained exact node-[173] state"
      description := "The ledger source contains the typed node-[173] residual together with equality to the actual node-[173] run. The anchor row is that retained state exactly; only non-anchor rows re-anchor node [170]'s complete local schedule."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowComponentD1D3LedgerSource.node173Exact,
        `Erdos64EG.Internal.computedP13SameWindowComponentD1D3LedgerSource,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_source_exact_node173,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_anchor_row_eq_retained,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_retained_anchor_agrees_actual_node173
      ]
    },
    {
      linkId := "proof-slice.p13-component-d1d3-ledger-d4d7-classifier"
      sourceStageId := "proof-slice.p13-same-window-component-d1d3-ledger"
      targetStageId := "proof-slice.p13-same-window-component-d4d7-classifier"
      kind := .frameworkComposition
      label := "consume the exact node-[174] split"
      description := "The source retains node [174]'s generic result and proves equality with the actual specialized P13 run. Both CT10 inputs preserve the identical branch context; no D4--D7 semantics are supplied by the caller."
      automationDeclarations := [
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseRouteContract,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingRouteContract
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_generic_node174,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_specialized_node174
      ]
    },
    {
      linkId := "proof-slice.p13-component-d4d7-classifier-readiness"
      sourceStageId := "proof-slice.p13-same-window-component-d4d7-classifier"
      targetStageId := "proof-slice.p13-same-window-component-d4d7-readiness"
      kind := .frameworkComposition
      label := "consume the exact node-[175] execution"
      description := "The readiness source stores equality with the actual specialized node-[175] run. It eliminates only the constructor contradicted by the retained anchor stub and preserves every remaining local witness and CT10 route."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7SemanticReadiness_exact_node175,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.source_exact
      ]
    },
    {
      linkId := "proof-slice.p13-packed-support-transition-owner-change"
      sourceStageId := "proof-slice.p13-same-window-packed-support-transition"
      targetStageId := "proof-slice.p13-same-window-packed-owner-change"
      kind := .frameworkComposition
      label := "exact all-inside constructor"
      description := "The input stores equality with node [168]'s actual all-inside result. The graph layer prepares the finite owner inventory and one stored unique owner for each vertex of that same return."
      automationDeclarations := [`StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.run]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
        `Erdos64EG.Internal.P13SameWindowComputedAllInside.graphInput
      ]
    },
    {
      linkId := "proof-slice.p13-owner-change-cross-window-token-pair"
      sourceStageId := "proof-slice.p13-same-window-packed-owner-change"
      targetStageId := "proof-slice.p13-same-window-cross-window-token-pair"
      kind := .frameworkComposition
      label := "exact first cross-window edge"
      description := "The source is node [169]'s complete first-cross-window package. The typed route only projects its two already computed endpoint tokens and records their opposite orientations on the same literal edge."
      automationDeclarations := [
        `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.route
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowFirstCrossWindow,
        `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange_exact
      ]
    },
    {
      linkId := "proof-slice.p13-base-scale-long-support-prefix"
      sourceStageId := "proof-slice.p13-same-window-base-scale-split"
      targetStageId := "proof-slice.p13-same-window-long-support-prefix"
      kind := .frameworkComposition
      label := "computed long constructor"
      description := "The input records equality with node [161]'s computed strict-long result. The generic route preserves the identical branch context and source while exposing the forced initial support segment."
      automationDeclarations := [
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.route
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
        `Erdos64EG.Internal.P13SameWindowLongOutput
      ]
    },
    {
      linkId := "proof-slice.p13-long-support-prefix-observed-label"
      sourceStageId := "proof-slice.p13-same-window-long-support-prefix"
      targetStageId := "proof-slice.p13-same-window-long-prefix-state-labels"
      kind := .frameworkComposition
      label := "exact first-nine prefix occurrences"
      description := "The source stores equality with node [163]'s actual run. The route inspects only the first nine literal corridor occurrences and passes exactly the collided pair to the CT10 refinement table."
      automationDeclarations := [
        `StructuralExhaustion.Routes.LongPrefixObservedLabel.route
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowLongPrefixStateSource.node163Exact,
        `Erdos64EG.Internal.p13SameWindowLongPrefixStateSource_exactNode163,
        `Erdos64EG.Internal.p13SameWindowLongPrefixObservedVertex_exact
      ]
    },
    {
      linkId := "proof-slice.p13-long-prefix-label-degree-refinement"
      sourceStageId := "proof-slice.p13-same-window-long-prefix-state-labels"
      targetStageId := "proof-slice.p13-same-window-long-prefix-degree-refinement"
      kind := .frameworkComposition
      label := "retain the exact collided occurrences"
      description := "The degree source contains the actual node-[164] result and its promoted CT10 response-context residual. The consumer reads exactly the two corridor vertices selected by that collision."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_node164,
        `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_ct10_promotion_responseContexts
      ]
    },
    {
      linkId := "proof-slice.p13-same-window-frontier-dyadic-terminal"
      sourceStageId := "proof-slice.p13-same-window-structural-frontier"
      targetStageId := "proof-slice.p13-same-window-dyadic-terminal"
      kind := .frameworkComposition
      label := "computed dyadic constructor"
      description := "Only the computed dyadic constructor is consumed. Its canonical stub position and restored root cycle form the exact G1 certificate passed to the existing proof-carrying CT1 runner."
      automationDeclarations := [
        `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.runCycleAsRootedReturnCT1
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit,
        `Erdos64EG.Internal.P13ComputedDyadicBranch.impossible
      ]
    },
    {
      linkId := "proof-slice.positive-deficiency-curvature"
      sourceStageId := "proof-slice.p13-positive-deficiency"
      targetStageId := "proof-slice.p13-curvature-rank"
      kind := .frameworkComposition
      label := "same exact remainder"
      description := "The graph accounting kernel consumes the unchanged CT12 remainder. Its boundary ledger is a subledger of the selected-window tokens, its raw wedge schedule has exactly W₂ entries, and CT15 scans precisely that schedule."
      automationDeclarations := [
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_tokenCount,
        `StructuralExhaustion.Graph.FiniteSupportResponse.Profile.run
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix,
        `Erdos64EG.Internal.exists_verifiedP13CurvaturePrefix
      ]
    },
    {
      linkId := "proof-slice.curvature-proper-delocalization"
      sourceStageId := "proof-slice.p13-curvature-rank"
      targetStageId := "proof-slice.proper-delocalization"
      kind := .frameworkComposition
      label := "rank-drop support classification"
      description := "The exact CT15 run proves that the rank-drop residual is empty on the selected minimal graph. The reusable conditional route nevertheless classifies every enlarged certificate and closes its proper-support constructor through CT3, leaving only the later whole-graph constructor."
      automationDeclarations := [
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.route
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix
      ]
    },
    {
      linkId := "proof-slice.proper-global-rank-drop"
      sourceStageId := "proof-slice.proper-delocalization"
      targetStageId := "proof-slice.global-rank-drop-closure"
      kind := .frameworkComposition
      label := "exact whole-support payload"
      description := "The whole constructor carries the admitted finite quotient and its literal rank-drop identification unchanged. The generic exact-label barrier derives injectivity from that admission certificate and closes the distinct identification."
      automationDeclarations := [
        `StructuralExhaustion.Graph.ClosedRankDrop.rankDrop_impossible
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix,
        `Erdos64EG.Internal.exists_verifiedP13GlobalRankClosurePrefix
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
      linkId := "proof-slice.high-center-dichotomy-degree-four-ledger"
      sourceStageId := "proof-slice.high-center-port-dichotomy"
      targetStageId := "proof-slice.degree-four-type-b-ledger"
      kind := .frameworkComposition
      label := "no degree-greater-than-four centre"
      description := "The negative high-centre branch is retained pointwise. The framework derives degree exactly four for every actual centre and runs the local CT14 fan ledger on that same finite centre schedule."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeBSupportScope.degree_eq_four_of_noHigher,
        `Erdos64EG.Internal.TypeBSupportScope.higher_or_degreeFour_certificateFlow
      ]
    },
    {
      linkId := "proof-slice.degree-four-ledger-b2-routing"
      sourceStageId := "proof-slice.degree-four-type-b-ledger"
      targetStageId := "proof-slice.degree-four-b2-routing"
      kind := .frameworkComposition
      label := "assigned certificate to exact local entry"
      description := "Every resolved local entry must name the exact Option certificate returned by node [80]. Finite resolution and CT12 then expose all negative and positive B2 outcomes."
      automationDeclarations := [
        `StructuralExhaustion.Core.FiniteResolution.Profile.fullResolution_or_unresolved,
        `StructuralExhaustion.CT12.RefinedLedgerCompletion.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedDegreeFourTypeBLedgerPrefix,
        `Erdos64EG.Internal.exists_verifiedDegreeFourB2RoutingPrefix
      ]
    },
    {
      linkId := "proof-slice.degree-four-b2-residual-center-ledger"
      sourceStageId := "proof-slice.degree-four-b2-routing"
      targetStageId := "proof-slice.type-b-residual-center-ledger"
      kind := .frameworkComposition
      label := "literal residual centers to surplus units"
      description := "Certificate failures, unresolved centers, and minimal-overlap demands remain subtypes of the actual high-center schedule, whose graph-derived assigned-surplus sum pays their cardinality."
      automationDeclarations := [
        `StructuralExhaustion.Graph.HighCenterDeletionCharge.Profile.centers_card_le_assignedSurplus
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedDegreeFourB2RoutingPrefix,
        `Erdos64EG.Internal.exists_verifiedTypeBResidualCenterLedgerPrefix
      ]
    },
    {
      linkId := "proof-slice.type-b-residual-center-ledger-local-fan-mass"
      sourceStageId := "proof-slice.type-b-residual-center-ledger"
      targetStageId := "proof-slice.type-b-local-fan-mass"
      kind := .frameworkComposition
      label := "retain the exact residual-center ledger"
      description := "The local CT14 endpoint stores the identical node-[75]/[81]--[83] VerifiedTypeBResidualCenterLedgerPrefix and scans only the selected centers produced inside each literal Type B scope. It does not manufacture the still-open canonical global support family."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedTypeBLocalFanMassPrefix,
        `Erdos64EG.Internal.TypeBSupportScope.localFanMassRoute
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
      sourceStageId := "proof-slice.surplus-scale-split"
      targetStageId := "proof-slice.sparse-envelope"
      kind := .frameworkComposition
      label := "consume the strict Part-X residual"
      description := "The node-[125] residual retains the literal strict node-[19] inequality and the same node-[18] selected graph. On that identical graph the route executes the existing CT6 surplus audit and the graph profile converts no-proper-core into one bounded elimination certificate for CT12."
      automationDeclarations := [
        `StructuralExhaustion.Graph.DegeneracyPeeling.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.routeSurplusScale_exhaustive,
        `Erdos64EG.Internal.sparseEnvelopeProfile,
        `Erdos64EG.Internal.sparseEnvelope_edgeBound,
        `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure,
        `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure_sameLabelPrefix
      ]
    },
    {
      linkId := "proof-slice.baseline-spine-demand"
      sourceStageId := "proof-slice.sparse-envelope"
      targetStageId := "proof-slice.baseline-spine-demand"
      kind := .frameworkComposition
      label := "declare and audit the exact baseline demand"
      description := "The retained selected graph supplies n to the cubic-baseline count. The application declares the canonical independent empty family and its exact full deficit; the reusable CT15 profile owns the full-rank execution, exact ledger, trace, soundness, totality, and linear work bound."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPortActivation.verifiedActivatedStageFromMinimality,
        `StructuralExhaustion.CT15.BaselineDemand.Profile.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedSurplusPortActivationPrefix,
        `Erdos64EG.Internal.exists_verifiedSurplusPortActivationPrefix,
        `Erdos64EG.Internal.baselineSpineProfile,
        `Erdos64EG.Internal.exists_verifiedBaselineSpineDemandPrefix
      ]
    },
    {
      linkId := "proof-slice.baseline-spine-demand-sparse-pair-responses"
      sourceStageId := "proof-slice.baseline-spine-demand"
      targetStageId := "proof-slice.sparse-pair-responses"
      kind := .frameworkComposition
      label := "consume the exact activated residual"
      description := "The pair stage uses the activated CT6 schedule retained by the baseline prefix on the same selected graph. The framework owns pair generation, the exact local partition, shortest connectors, quotient admissibility, and CT15 execution."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPairResponse.verifiedStage,
        `StructuralExhaustion.CT15.AdmissibleQuotient.Profile.verifiedFor
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedBaselineSpineDemandPrefix,
        `Erdos64EG.Internal.sparsePairResponseStage,
        `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix
      ]
    },
    {
      linkId := "proof-slice.sparse-pair-responses-total-pair-token-route"
      sourceStageId := "proof-slice.sparse-pair-responses"
      targetStageId := "proof-slice.total-pair-token-route"
      kind := .frameworkComposition
      label := "route both blocker decisions"
      description := "The CT9 product ledger consumes the exact node-130 pair schedule. Its freeAnchor constructor is definitionally the negative blocker result and its blocked constructor retains the canonical first hit, so both routes use only the preceding verified output."
      automationDeclarations := [
        `StructuralExhaustion.CT9.TokenRoleLedger.noOvercounting,
        `StructuralExhaustion.Graph.SurplusPairTokenRouting.noOvercounting
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix,
        `Erdos64EG.Internal.allPairTokenRouting_freeHandoff,
        `Erdos64EG.Internal.allPairTokenRouting_blockedHandoff,
        `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix
      ]
    },
    {
      linkId := "proof-slice.total-pair-token-route-capacity-token-ledger"
      sourceStageId := "proof-slice.total-pair-token-route"
      targetStageId := "proof-slice.capacity-token-ledger"
      kind := .frameworkComposition
      label := "refine the exact complete pair ledger"
      description := "The capacity-token stage consumes the unchanged node-130 pair collection. Free pairs keep their already verified selected-port token; blocked pairs use their retained canonical first hit and the deterministic window/remainder/primitive priority map."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix,
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.input_items_eq_source,
        `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix
      ]
    },
    {
      linkId := "proof-slice.capacity-token-ledger-coupled-class-overload"
      sourceStageId := "proof-slice.capacity-token-ledger"
      targetStageId := "proof-slice.coupled-class-overload"
      kind := .frameworkComposition
      label := "execute the exact 25-role coupled decision"
      description := "The classwise CT9 profile uses precisely the complete pair list, token map, role map, and 25-role enumeration certified by the preceding green stage. No entropy realization, global graph family, or extra branch assumption is introduced."
      automationDeclarations := [
        `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.decide,
        `StructuralExhaustion.Graph.SurplusClasswiseOverload.verifiedStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix,
        `Erdos64EG.Internal.coupledPairCount_eq_chooseSurplus,
        `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix
      ]
    },
    {
      linkId := "proof-slice.coupled-class-overload-homogeneous-pattern"
      sourceStageId := "proof-slice.coupled-class-overload"
      targetStageId := "proof-slice.homogeneous-pattern"
      kind := .frameworkComposition
      label := "scan the actual overloaded fibre"
      description := "The consumer receives the exact CT9 fibre and its already verified token-class constructor. The generic graph theorem derives the matching or star from only that local list."
      automationDeclarations := [
        `StructuralExhaustion.Core.GreedyMatchingStar.verifiedStage,
        `StructuralExhaustion.Graph.SurplusHomogeneousPattern.audit
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix,
        `Erdos64EG.Internal.exists_verifiedHomogeneousPatternPrefix
      ]
    },
    {
      linkId := "proof-slice.homogeneous-pattern-coarse-bottleneck-classification"
      sourceStageId := "proof-slice.homogeneous-pattern"
      targetStageId := "proof-slice.coarse-bottleneck-classification"
      kind := .frameworkComposition
      label := "classify the exact homogeneous pattern"
      description := "The fixed coarse classifier stores the identical VerifiedHomogeneousPatternPrefix and consumes its actual 49-pair matching-or-star audit. The only search is the prescribed 49-element pattern against the exact 48-state local structural code."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.verifiedCollision
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.exists_verifiedGeometricBottleneckClassificationPrefix,
        `Erdos64EG.Internal.coarseBottleneckClassification
      ]
    },
    {
      linkId := "proof-slice.coarse-bottleneck-semantic-classification"
      sourceStageId := "proof-slice.coarse-bottleneck-classification"
      targetStageId := "proof-slice.semantic-bottleneck-classification"
      kind := .frameworkComposition
      label := "consume the exact typed semantic trigger"
      description := "Node [177] receives node [144]'s actual collision trigger, unchanged attachment maps, and identical two rooted germs. It scans only the declared attachment coordinates and retains the exact five-way residual."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_source_exact,
        `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify_source_exact,
        `Erdos64EG.Internal.semanticBottleneck_residual_exact,
        `Erdos64EG.Internal.semanticBottleneck_source_exact,
        `Erdos64EG.Internal.semanticBottleneck_germ_source_exact
      ]
    },
    {
      linkId := "proof-slice.semantic-classification-local-consumer"
      sourceStageId := "proof-slice.semantic-bottleneck-classification"
      targetStageId := "proof-slice.semantic-bottleneck-local-consumer"
      kind := .frameworkComposition
      label := "consume all five exact node-[177] leaves"
      description := "The consumer stores equality with node [177]'s actual classification and performs only the finite incidence/degree checks exposed by the selected leaf."
      evidenceDeclarations := [
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_previous_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalConsumer_frontier_exact
      ]
    },
    {
      linkId := "proof-slice.semantic-local-consumer-normalization"
      sourceStageId := "proof-slice.semantic-bottleneck-local-consumer"
      targetStageId := "proof-slice.semantic-bottleneck-switch-normalization"
      kind := .frameworkComposition
      label := "normalize the exact node-[178] switch"
      description := "The source stores equality with node [178]'s actual frontier; normalization only repackages its already proved incidences and degree branch."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckNormalizationSource_node178_exact]
    },
    {
      linkId := "proof-slice.component-d4d7-readiness-clause-schedule"
      sourceStageId := "proof-slice.p13-same-window-component-d4d7-readiness"
      targetStageId := "proof-slice.p13-component-d4d7-clause-schedule"
      kind := .frameworkComposition
      label := "schedule the exact missing-clause markers"
      description := "The source stores equality with node [180]'s actual result and retains each dependent marker while assigning only the fixed four-slot obligation order."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseSchedule_exact_node180]
    },
    {
      linkId := "proof-slice.long-prefix-degree-local-alignment"
      sourceStageId := "proof-slice.p13-same-window-long-prefix-degree-refinement"
      targetStageId := "proof-slice.p13-long-prefix-local-clause-alignment"
      kind := .frameworkComposition
      label := "compare the exact pair on nine literal coordinates"
      description := "The source stores equality with node [179]'s actual runner and reuses the exact first-nine occurrence map and retained CT10 obligation."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.exact_node179,
        `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.retained_ct10_responseContexts
      ]
    },
    {
      linkId := "proof-slice.semantic-normalization-local-projection"
      sourceStageId := "proof-slice.semantic-bottleneck-switch-normalization"
      targetStageId := "proof-slice.semantic-bottleneck-local-projection"
      kind := .frameworkComposition
      label := "project the exact node-[181] leaves"
      description := "The source stores equality with node [181]'s actual normalized result and projects only its literal cubic support or declared high ports."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckLocalProjectionSource_node181_exact]
    },
    {
      linkId := "proof-slice.d4d7-schedule-cursor"
      sourceStageId := "proof-slice.p13-component-d4d7-clause-schedule"
      targetStageId := "proof-slice.p13-component-d4d7-clause-cursor"
      kind := .frameworkComposition
      label := "focus D4 in the exact node-[182] ledgers"
      description := "The cursor preserves every dependent marker and the exact D5--D7 tail; it supplies no clause truth."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseCursor_exact_node182]
    },
    {
      linkId := "proof-slice.local-alignment-extended-alignment"
      sourceStageId := "proof-slice.p13-long-prefix-local-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-extended-clause-alignment"
      kind := .frameworkComposition
      label := "extend only to literal positions 9--17"
      description := "The source stores equality with node [183]'s actual result and retains the nested degree and CT10 provenance."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.exact_node183]
    },
    {
      linkId := "proof-slice.local-projection-strong-frontier"
      sourceStageId := "proof-slice.semantic-bottleneck-local-projection"
      targetStageId := "proof-slice.semantic-bottleneck-strong-frontier"
      kind := .frameworkComposition
      label := "tag each exact leaf's pending obligation"
      description := "The exact node-[184] projection and payload pass unchanged; the tag records which theorem remains to be proved and supplies no certificate."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckStrongFrontierSource_node184_exact]
    },
    {
      linkId := "proof-slice.d4-cursor-local-request"
      sourceStageId := "proof-slice.p13-component-d4d7-clause-cursor"
      targetStageId := "proof-slice.p13-component-d4-local-clause-request"
      kind := .frameworkComposition
      label := "request evaluation of the actual D4 head"
      description := "Each actual cursor yields one singleton D4 request and keeps its dependent marker and exact D5--D7 tail; no Boolean is accepted."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4LocalClauseRequest_exact_node185]
    },
    {
      linkId := "proof-slice.extended-alignment-third-block"
      sourceStageId := "proof-slice.p13-long-prefix-extended-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-third-block-clause-alignment"
      kind := .frameworkComposition
      label := "extend only to literal positions 18--26"
      description := "The exact node-[186] result passes through with all nested degree and CT10 provenance; only the third nine-coordinate block is newly inspected."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.exact_node186]
    },
    {
      linkId := "proof-slice.strong-frontier-first-clause"
      sourceStageId := "proof-slice.semantic-bottleneck-strong-frontier"
      targetStageId := "proof-slice.semantic-bottleneck-first-clause"
      kind := .frameworkComposition
      label := "expose the first literal separator clause"
      description := "The exact node-[187] payload and obligation tag are retained while only fixed-arity incidence data are exposed."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckFirstClauseSource_node187_exact]
    },
    {
      linkId := "proof-slice.d4-request-evaluator-residual"
      sourceStageId := "proof-slice.p13-component-d4-local-clause-request"
      targetStageId := "proof-slice.p13-component-d4-evaluator-residual"
      kind := .frameworkComposition
      label := "expose the missing graph-derived evaluator contract"
      description := "Every exact request, marker, and tail is retained; only graph-local predicate and provenance requirements are added."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4EvaluatorResidual_exact_node188]
    },
    {
      linkId := "proof-slice.third-block-fourth-block"
      sourceStageId := "proof-slice.p13-long-prefix-third-block-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      kind := .frameworkComposition
      label := "extend only to literal positions 27--35"
      description := "The exact node-[189] result and nested CT10 provenance pass through; only the fourth nine-coordinate block is inspected."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.exact_node189]
    },
    {
      linkId := "proof-slice.first-clause-pairwise-clause"
      sourceStageId := "proof-slice.semantic-bottleneck-first-clause"
      targetStageId := "proof-slice.semantic-bottleneck-pairwise-clause"
      kind := .frameworkComposition
      label := "derive only literal pairwise inequalities"
      description := "The exact node-[190] certificate and pending tag pass through; injectivity and adjacency yield only the fixed-arity pairwise clauses."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckPairwiseClauseSource_node190_exact]
    },
    {
      linkId := "proof-slice.d4-residual-construction-residual"
      sourceStageId := "proof-slice.p13-component-d4-evaluator-residual"
      targetStageId := "proof-slice.p13-component-d4-evaluator-construction-residual"
      kind := .frameworkComposition
      label := "name the graph-owned construction inputs"
      description := "Each exact node-[191] residual is retained and refined into component-local data, graph-owned predicate definition, and predicate derivation requirements."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191]
    },
    {
      linkId := "proof-slice.fourth-block-compatible-response-frontier"
      sourceStageId := "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-compatible-response-frontier"
      kind := .frameworkComposition
      label := "freeze the exact response residual"
      description := "All five node-[192] leaves, degree provenance, and CT10 response-context tag are retained while the missing graph-owned semantic inputs are made explicit."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192]
    }
  ]
}

private def erdosManuscript : ExampleManuscriptDescriptor := {
  title := "Erdős--Gyárfás Problem 64 proof"
  path := "proofs/erdos_64_eg/erdos_64_proof.tex"
  /- Whole-node status for the Chapter 1 web diagram.  Manuscript references
  below may additionally index partial Lean coverage; those nodes remain
  yellow until every assertion displayed in the diagram cell is proved. -/
  formalizedNodeIds := [
    1, 2, 3,
    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35,
    36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    67, 68, 69, 70, 71, 72, 73, 74, 75, 78, 79, 80, 81, 82, 83, 84,
    125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136,
    137, 138, 139, 140, 141, 142, 143, 144, 155, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195
  ]
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
            `StructuralExhaustion.Core.IsCounterexample,
            `StructuralExhaustion.Core.target_of_not_isCounterexample,
            `Erdos64EG.Internal.IsCounterexample,
            `Erdos64EG.Internal.officialConclusion_of_notCounterexample,
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
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.Certificate.contextAudit,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.impossible,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.route
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
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_polynomial,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.terminal,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.trace,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.checks,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.polynomial,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.AtAtom.total
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
            `Erdos64EG.Internal.boundariedReplacementPrefix_uncompressible,
            `Erdos64EG.Internal.verifiedRankDropRoutingStage,
            `Erdos64EG.Internal.rankDropRoutingPrefix_previous,
            `Erdos64EG.Internal.rankDropRoutingPrefix_stage
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
        "This covers nodes [11]--[14] for normalized decompositions with nonempty boundary and the complete certificate-local routing at nodes [36]--[39]. A context mismatch yields the exact target-defective residual; a context-universal at-atom realization executes CT3 and contradicts minimality; an enlarged-support residual is retained unchanged for node [40]. Empty-boundary closed representatives remain a separate later manuscript branch."
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
            `Erdos64EG.Internal.p13Remainder_internalSubgraphThreeCore_free,
            `StructuralExhaustion.Graph.InducedPathPacking.remainder_card_ge_of_packingNumber_le,
            `Erdos64EG.Internal.P13CoverageResidual,
            `Erdos64EG.Internal.verifiedP13RemainderResidual,
            `Erdos64EG.Internal.p13Remainder_large,
            `Erdos64EG.Internal.p13Remainder_node26_exact
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
        "The packing and P₁₃-free remainder clauses are implemented. Nodes [25]--[26] consume the exact predecessor ceiling p₁₃ ≤ U₁₃ and derive the certified finite floor |V(G)| - 13U₁₃ ≤ |R| on the identical CT12 remainder. Producing the numerical ceiling remains node [24]'s separate task."
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
        "Node [18]'s legal-label table and Cₛ/Ω₂ definitions are implemented. Node [21]'s complete 91-barrier curvature table is the separate green step erdos.p13-multiscale-curvature."
      workBound := "8192 + 399 + 399² = 167792 primitive checks; quadratic in the explicit 8192-code universe."
    },
    {
      stepId := "erdos.surplus-scale-split"
      stageId? := some "proof-slice.surplus-scale-split"
      title := "Exact surplus decision and Part-X entry"
      plainExplanation := "After node [18], the framework reads the actual total degree surplus and graph order. One natural-number comparison decides the two branches. Its strict outcome is retained verbatim at node [20] and node [125]; the complementary inequality is retained as the exact node-[21] input."
      formalStatement := "C_{\\rm sp}^2 n<\\sigma(G)^2\\ \\lor\\ \\sigma(G)^2\\le C_{\\rm sp}^2 n"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:near-cubic-spine", title := "Near-cubic surplus scale", nodeIds := [19, 20] },
        { label := "thm:sharp-classwise-homogeneous-token-budget", title := "Explicit homogeneous-cap coefficient", nodeIds := [19, 125] }
      ]
      declarationGroups := [{
        groupId := "quadratic-surplus-scale"
        title := "Reusable constant-work squared-scale decision"
        role := .semanticTheorem
        explanation := "The core stage owns the exhaustive comparison and one-check work audit. The Erdős instance supplies only the actual surplus, graph order, and the same explicit cap coefficient consumed downstream at node [138]."
        declarations := [
          `StructuralExhaustion.Core.QuadraticScaleSplit.decide,
          `StructuralExhaustion.Core.QuadraticScaleSplit.exhaustive,
          `StructuralExhaustion.Core.QuadraticScaleSplit.verifiedStage,
          `Erdos64EG.Internal.surplusScaleCoefficient,
          `Erdos64EG.Internal.surplusScaleInput,
          `Erdos64EG.Internal.surplusScaleStage,
          `Erdos64EG.Internal.surplusScale_exhaustive,
          `Erdos64EG.Internal.routeSurplusScale,
          `Erdos64EG.Internal.routeSurplusScale_exhaustive,
          `Erdos64EG.Internal.exists_verifiedP13LabelAlgebraPrefix,
          `Erdos64EG.Internal.exists_verifiedSurplusScaleSplitPrefix,
          `Erdos64EG.Internal.verifiedSurplusScaleRoutingPrefix,
          `Erdos64EG.Internal.exists_verifiedSurplusScaleRoutingPrefix
        ]
      }]
      scopeNotes := "Nodes [19], [20], and [125] are complete as one local typed route. The strict inequality and predecessor are preserved definitionally into Part X; the bounded inequality remains the separate node-[21] residual."
      workBound := "One exact natural-number comparison. No square root, floating-point computation, graph family, or threshold search is evaluated."
    },
    {
      stepId := "erdos.p13-multiscale-curvature"
      stageId? := some "proof-slice.p13-multiscale-curvature"
      title := "Complete 91-barrier P13 curvature certificate"
      plainExplanation := "On the bounded constructor of the exact node-[19] surplus split, CT10 classifies all 196 ordered candidate length pairs and retains exactly the 91 pairs a,b≥1 with a+b≤14. Fifteen fixed 399-row relation matrices are audited bit-for-bit against the graph attachment semantics. Independent shards audit every accepted safe and composition-flat count against the reusable finite-relation barrier, including the existing 543958/432672/111286 scale-(1,1) counts. Exact integer arithmetic proves that the product barrier is larger than 2^118, without evaluating a logarithm or assuming any Boolean-state realization."
      formalStatement := "|\\{(a,b):a,b\\ge1,\\ a+b\\le14\\}|=91,\\qquad 2^{118}\\prod F_{a,b}<\\prod S_{a,b}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:curv-enum", title := "Finite curvature enumeration", nodeIds := [21] },
        { label := "app:curv-code", title := "Curvature computation", nodeIds := [21] }
      ]
      declarationGroups := [
        {
          groupId := "multiscale-relation-semantics"
          title := "Sparse bit relation and graph semantics"
          role := .semanticTheorem
          explanation := "The sparse forbidden-gap decision is proved equivalent to the public power-of-two attachment relation at every used scale; the generated rows are then rechecked against that decision."
          declarations := [
            `Erdos64EG.Internal.p13CodeCompatibleSparse_iff,
            `Erdos64EG.Internal.p13CodeCompatibleFast_iff,
            `Erdos64EG.Internal.p13MultiScaleRows_codeAudit,
            `Erdos64EG.Internal.p13MultiScaleCompatibilityRow_semantic
          ]
        },
        {
          groupId := "multiscale-count-audits"
          title := "Generic safe/flat barrier audits"
          role := .executionAudit
          explanation := "All 91 literal counts are connected back to the reusable finite bit-relation profile; the fixed arrays are not trusted as assumptions."
          declarations := [
            `StructuralExhaustion.Core.FiniteBitRelationBarrier.Profile.safeCount,
            `StructuralExhaustion.Core.FiniteBitRelationBarrier.Profile.flatCount,
            `Erdos64EG.Internal.p13MultiScaleSafeCounts_audit,
            `Erdos64EG.Internal.p13MultiScaleFlatCounts_audit,
            `Erdos64EG.Internal.p13BarrierSafeCount_audit,
            `Erdos64EG.Internal.p13BarrierFlatCount_audit
          ]
        },
        {
          groupId := "multiscale-ct10-endpoint"
          title := "CT10 classification and exact branch route"
          role := .compositionProvenance
          explanation := "The CT10 endpoint retains the exact bounded node-[19] residual. The combined router preserves the strict Part-X residual unchanged and replaces only the bounded constructor by the verified curvature certificate."
          declarations := [
            `Erdos64EG.Internal.p13Barrier_class_count,
            `Erdos64EG.Internal.p13Barrier_one_one_counts,
            `Erdos64EG.Internal.p13MultiScaleBarrier_more_than_118_bits,
            `Erdos64EG.Internal.verifiedP13MultiScaleCurvaturePrefix,
            `Erdos64EG.Internal.routeSurplusScale,
            `Erdos64EG.Internal.routeSurplusScaleThroughCurvature,
            `Erdos64EG.Internal.routeSurplusScaleThroughCurvature_exhaustive
          ]
        }
      ]
      scopeNotes := "Node [21] is complete on the exact bounded node-[19] constructor. The still-open multi-scale realization and commuting-gluing claims of lem:p13-window-package, including node [22], are deliberately not cited by this step. It asks for neither global nor local Boolean-product realization. The strict constructor remains the already verified Part-X sparse-pressure route."
      workBound := "Fifteen fixed 399×399 bit relations and 91 quadratic barrier scans, split into 15 independently cached audit shards. The public CT10 classification uses 196 candidate checks; no graph family or Boolean cube is enumerated."
    },
    {
      stepId := "erdos.p13-actual-attachment-cold-fork"
      stageId? := some "proof-slice.p13-actual-attachment-cold-fork"
      title := "Pointwise actual P13 attachment cold fork"
      plainExplanation := "For one exact selected induced-P13 window, the classifier scans actual outside vertices against the thirteen literal path-adjacency bits. A hot certificate would realize the all-true assignment; positions 0 and 2 then produce a four-cycle, contradicting target avoidance. The classifier therefore returns its canonical missing assignment and retains the exact same selected window."
      formalStatement := "\\forall P\\in\\mathcal P,\\quad \\exists\\varepsilon\\in\\{0,1\\}^{13}\\quad \\forall x\\notin P,\\;\\rho_P(x)\\ne\\varepsilon"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-actual-attachment-cold-fork", title := "Pointwise actual-attachment cold fork", nodeIds := [158] },
        { label := "rem:p13-actual-attachment-fork-scope", title := "Scope of the actual-attachment fork", nodeIds := [158] }
      ]
      declarationGroups := [
        {
          groupId := "p13-actual-attachment-semantics"
          title := "Actual thirteen-bit adjacency system"
          role := .semanticTheorem
          explanation := "The system's coordinates are exactly the thirteen path positions and its response bits are literal graph adjacency."
          declarations := [
            `Erdos64EG.Internal.p13ActualAttachmentSystem_value_eq_true_iff,
            `Erdos64EG.Internal.p13ActualAttachmentSystem_coordinateCard
          ]
        },
        {
          groupId := "p13-actual-attachment-classifier"
          title := "Finite classifier and hot impossibility"
          role := .executionAudit
          explanation := "The reusable finite Boolean classifier is executed, and its hot constructor is eliminated by the graph-owned four-cycle theorem."
          declarations := [
            `StructuralExhaustion.Core.LocalBooleanRealization.System.classify,
            `Erdos64EG.Internal.p13RawAttachmentSystem_hot_impossible,
            `Erdos64EG.Internal.p13ActualAttachmentColdFork,
            `Erdos64EG.Internal.p13ActualAttachment_classify_cold
          ]
        },
        {
          groupId := "p13-actual-attachment-provenance"
          title := "Exact predecessor, missing assignment, and same window"
          role := .compositionProvenance
          explanation := "The node-[21] predecessor is retained, the cold assignment is absent from every actual state, and the selected window is unchanged."
          declarations := [
            `Erdos64EG.Internal.verifiedP13MultiScaleCurvaturePrefix,
            `Erdos64EG.Internal.p13ActualAttachmentColdFork_missing,
            `Erdos64EG.Internal.p13ActualAttachmentColdFork_same_selected_window
          ]
        },
        {
          groupId := "p13-actual-attachment-work"
          title := "Linear reference work bound"
          role := .executionAudit
          explanation := "The finite state count is bounded by the ambient vertex count and the complete assignment/state/coordinate scan has the stated linear bit-comparison budget."
          declarations := [
            `Erdos64EG.Internal.p13ActualAttachmentColdFork_states_card_le_vertices,
            `Erdos64EG.Internal.p13ActualAttachmentColdForkCheckBudget,
            `Erdos64EG.Internal.p13ActualAttachmentColdForkCheckBudget_linear
          ]
        }
      ]
      scopeNotes := "Node [158] is a pointwise actual thirteen-bit adjacency scan. The production same-context adapter maps every exact node-[21] packed window through this cold fork and node [159], and proves that its four structural subledgers partition exactly p13 windows. This neither proves nor refutes the still-white node-[160] 91-coordinate realization edge [21]→[22], and it yields no entropy or density bound."
      workBound := "Worst-case reference budget for one supplied selected window: at most 8192·n assignment/state vector comparisons, each comparing thirteen adjacency bits; equivalently at most 106496·n bit comparisons. The subsequent corridor/path work at node [159] is excluded."
    },
    {
      stepId := "erdos.p13-node21-partxi-route"
      stageId? := some "proof-slice.p13-node21-partxi-route"
      title := "Exact whole-packing route into Part XI"
      plainExplanation := "The production adapter maps the exact CT12 packing list. Each entry retains the node-[21] prefix, classifier-produced thirteen-bit cold residual, identical selected window, and computed node-[159] structural frontier. Filtering by the four honest constructors gives an exact partition of all p13 windows."
      formalStatement := "|P_surplus| + |P_dyadic| + |P_high| + |P_quiet| = p13"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-actual-attachment-cold-fork", title := "Pointwise actual-attachment cold fork", nodeIds := [158] },
        { label := "lem:p13-same-window-structural-frontier", title := "Same-window structural frontier", nodeIds := [159] }
      ]
      declarationGroups := [{
        groupId := "p13-node21-partxi-route-execution"
        title := "Same-context packing map and exact four-way partition"
        role := .compositionProvenance
        explanation := "The route maps only the supplied packing list. It preserves each computed cold fork and frontier, then filters their stored constructor tags; it does not enumerate graph, completion, support, or context families."
        declarations := [
          `Erdos64EG.Internal.P13Node21PartXIEntry,
          `Erdos64EG.Internal.p13Node21PartXIEntry,
          `Erdos64EG.Internal.p13Node21PartXIRoutes,
          `Erdos64EG.Internal.p13Node21PartXIRoutes_length,
          `Erdos64EG.Internal.P13Node21PartXIEntry.outcomeTag,
          `Erdos64EG.Internal.p13Node21PartXIRoutesWithTag,
          `Erdos64EG.Internal.p13Node21PartXIRoutes_partition
        ]
      }]
      scopeNotes := "This is the exact valid parallel handoff from node [21] into nodes [158]--[159]. It uses thirteen literal adjacency bits, not node [160]'s still-missing 91 multi-scale completion responses, and it assigns no entropy or density payment to any constructor."
      workBound := "One traversal of the exact packing list plus the already charged fixed thirteen-bit cold fork and node-[159] local work for each supplied window; no additional candidate universe is materialized."
    },
    {
      stepId := "erdos.p13-same-window-structural-frontier"
      stageId? := some "proof-slice.p13-same-window-structural-frontier"
      title := "Same-window P13 structural frontier"
      plainExplanation := "The exact node-[158] cold fork indexes a graph-owned continuation on the same selected window. It returns exactly one of four constructors: a high-degree window position, a dyadic root-cycle hit, the first high-degree corridor vertex with its clean prefix, or a quiet structural germ carrying only an ambient-size support bound."
      formalStatement := "\\mathcal R(P)\\in\\{\\operatorname{surplus}(i),\\operatorname{dyadic}(s,C),\\operatorname{corridorHigh}(s,x),\\operatorname{quiet}(s,\\Gamma)\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-same-window-structural-frontier", title := "Same-window structural frontier", nodeIds := [159] },
        { label := "rem:p13-same-window-frontier-scope", title := "Scope of the same-window frontier", nodeIds := [159] }
      ]
      declarationGroups := [
        {
          groupId := "p13-same-window-graph-runner"
          title := "Graph-owned degree, stub, and corridor runners"
          role := .frameworkInterface
          explanation := "The framework classifies the thirteen actual degrees, selects the canonical cubic stub, constructs its deleted-edge return from bridgelessness, and scans the return for the first event. The Erdős adapter supplies only the fixed power-of-two predicate and selected window."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdStubSelection.classify,
            `StructuralExhaustion.Graph.InducedPathColdCorridor.runFirstFailure,
            `Erdos64EG.Internal.routeSelectedWindowCorridor,
            `Erdos64EG.Internal.routeSelectedWindowCorridor_exhaustive
          ]
        },
        {
          groupId := "p13-same-window-four-way-execution"
          title := "Cold-fork-indexed four-way execution"
          role := .tacticExecution
          explanation := "The result type is indexed by the exact node-[158] cold fork. The thin runner flattens the graph result into precisely the four published constructors and proves their exhaustive disjunction."
          declarations := [
            `Erdos64EG.Internal.p13ActualAttachmentColdFork,
            `Erdos64EG.Internal.P13SameWindowStructuralFrontier,
            `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
            `Erdos64EG.Internal.runP13SameWindowStructuralFrontier_exhaustive
          ]
        },
        {
          groupId := "p13-same-window-event-provenance"
          title := "Exact stub and first-hit provenance"
          role := .compositionProvenance
          explanation := "The dyadic and corridor-high payloads are reconstructed from their F1/F4 proofs on the same canonical stub, and every first hit retains the framework's clean earlier prefix."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowStructuralFrontier.dyadic_target_same_stub,
            `Erdos64EG.Internal.P13SameWindowStructuralFrontier.high_handoff_same_stub,
            `Erdos64EG.Internal.P13SameWindowStructuralFrontier.dyadic_prefix_clear
          ]
        },
        {
          groupId := "p13-same-window-visible-work"
          title := "Certificate-verification work bound"
          role := .workBound
          explanation := "The simple return is consumed as a proof-carrying certificate. The visible scans cover two thirteen-position passes, the existing external-incidence schedule, and at most n return stages; no constructive path-search runtime is claimed."
          declarations := [
            `Erdos64EG.Internal.p13CorridorCertificateChecks,
            `Erdos64EG.Internal.p13CorridorCertificateChecks_le_vertices,
            `Erdos64EG.Internal.p13SameWindowStructuralVisibleChecks,
            `Erdos64EG.Internal.p13SameWindowStructuralVisibleChecks_eq
          ]
        }
      ]
      scopeNotes := "Node [159] is green only for this pointwise four-way classifier. The window-surplus and corridor-high outputs remain typed open handoffs, and the quiet output is only ColdStructuralGerm, not a constant ColdBoundedGerm. No density, cold-mass, bounded-overlap, or aggregate nodes-[153]–[157] claim follows. Node [160] remains the white 91-bit realization obligation."
      workBound := "For one supplied selected window, at most 26 + (15·p13 + σW) + n visible local checks: two possible thirteen-position passes, one scan of the existing token schedule, and at most n event checks on the proof-carrying simple return."
    },
    {
      stepId := "erdos.p13-same-window-base-scale-split"
      stageId? := some "proof-slice.p13-same-window-base-scale-split"
      title := "Quiet-germ D1–D3 base-scale split"
      plainExplanation := "When the computed node-[159] result is its quiet constructor, the proof-carrying input retains the exact cold fork, selected window, canonical stub, no-event proof, structural germ, and equality to that run output. One graph-owned comparison at Qbase=4²·13²·2¹³ returns either the literal support bound at most Qbase or the strict long-support inequality."
      formalStatement := "Q_{\\rm base}=4^2 13^2 2^{13},\\qquad |\\operatorname{supp}(\\Gamma)|\\le Q_{\\rm base}\\;\\lor\\;Q_{\\rm base}<|\\operatorname{supp}(\\Gamma)|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-d1d3-base-scale-split", title := "D1–D3 base-scale split", nodeIds := [161] },
        { label := "rem:p13-d1d3-base-scale-scope", title := "Scope of the D1–D3 split", nodeIds := [161] }
      ]
      declarationGroups := [
        {
          groupId := "p13-d1d3-base-cardinality"
          title := "Exact D1–D3 normalized-state cardinal"
          role := .semanticTheorem
          explanation := "The fixed two-boundary cardinality theorem is specialized to an empty additional local-coordinate type, yielding exactly the two capped degrees, two window offsets, and thirteen target bits. This is not a D4–D7 completeness claim."
          declarations := [
            `StructuralExhaustion.Core.FixedTwoBoundaryCutState.state_card,
            `Erdos64EG.Internal.p13ColdD1D3BaseThreshold,
            `Erdos64EG.Internal.p13ColdD1D3BaseThreshold_eq_stateCard
          ]
        },
        {
          groupId := "p13-quiet-run-provenance"
          title := "Computed quiet-constructor provenance"
          role := .compositionProvenance
          explanation := "The scale input cannot be an arbitrary germ: it stores equality with the actual node-[159] quiet output and retains its fork, window, canonical stub, no-event proof, and germ."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
            `Erdos64EG.Internal.P13SameWindowQuietOutput
          ]
        },
        {
          groupId := "p13-d1d3-base-scale-execution"
          title := "Exact short/long support execution"
          role := .tacticExecution
          explanation := "The existing graph route compares the literal corridor support with Qbase. The two constructors retain either the non-strict bounded same-interface residual or the strict long-support residual, and exhaust all outcomes."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdGermScale.BoundedSameInterfaceResidual,
            `StructuralExhaustion.Graph.InducedPathColdGermScale.LongSupportResidual,
            `StructuralExhaustion.Graph.InducedPathColdGermScale.route,
            `Erdos64EG.Internal.P13SameWindowBaseScaleSplit,
            `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
            `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit_exhaustive
          ]
        },
        {
          groupId := "p13-d1d3-base-scale-work"
          title := "One-comparison work ledger"
          role := .workBound
          explanation := "Node [161] charges only the single natural-number support comparison; construction and scanning of the proof-carrying corridor were already charged at node [159]."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount,
            `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount_eq_one
          ]
        }
      ]
      scopeNotes := "Node [161] is only the exact D1–D3 support split on the computed quiet branch. It proves no repetition, D4–D7 semantic completeness, bounded-germ promotion, CT3 compression, or density estimate. Its literal short and long residuals feed the separately verified local nodes [162] and [163], while node [160] remains the white 91-bit realization obligation."
      workBound := "Exactly one natural-number comparison of the retained support length with the fixed constant Qbase=4²·13²·2¹³. No graph, path, state, response, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-short-third-incidence"
      stageId? := some "proof-slice.p13-same-window-short-third-incidence"
      title := "Short-return third-root incidence"
      plainExplanation := "Equality with node [161]'s computed short constructor fixes the exact bounded deleted-edge return. Minimum degree and the quiet no-high proof make its root cubic. The first return step and restored dart are two distinct incidences, so the declared-order root classifier selects the third and tests only whether that endpoint lies on the supplied return support."
      formalStatement := "x_3\\in\\operatorname{supp}(\\Gamma)\\;\\lor\\;x_3\\notin\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-short-third-incidence", title := "Short-return third incidence", nodeIds := [162] },
        { label := "rem:p13-short-third-incidence-scope", title := "Scope of the short-root split", nodeIds := [162] }
      ]
      declarationGroups := [
        {
          groupId := "p13-short-root-framework-classifier"
          title := "Graph-owned cubic-root classifier"
          role := .frameworkInterface
          explanation := "The generic graph setup reconstructs the two distinct root directions, proves the root cubic, selects the declared-order third incidence, and tests that one endpoint against the supplied support."
          declarations := [
            `StructuralExhaustion.Graph.RootIncidence.classify,
            `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Setup,
            `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Setup.degree_eq_three,
            `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.Result,
            `StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence.run
          ]
        },
        {
          groupId := "p13-short-root-provenance"
          title := "Exact computed-short provenance"
          role := .compositionProvenance
          explanation := "The input stores equality with node [161]'s short result. The identical quiet germ supplies root membership and the no-high fact, while the residual supplies the exact Qbase support bound."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
            `Erdos64EG.Internal.P13SameWindowComputedShort,
            `Erdos64EG.Internal.P13SameWindowComputedShort.root_degree_ge_three,
            `Erdos64EG.Internal.P13SameWindowComputedShort.root_mem_corridor,
            `Erdos64EG.Internal.P13SameWindowComputedShort.root_not_high,
            `Erdos64EG.Internal.P13SameWindowComputedShort.setup,
            `Erdos64EG.Internal.P13SameWindowComputedShort.return_support_bounded
          ]
        },
        {
          groupId := "p13-short-root-execution"
          title := "On-support/outside execution"
          role := .tacticExecution
          explanation := "The thin Erdős result exposes exactly the on-support and outside-boundary constructors and proves their exhaustive disjunction."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowShortThirdIncidence,
            `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
            `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence_exhaustive
          ]
        },
        {
          groupId := "p13-short-root-work"
          title := "Single-root work bound"
          role := .workBound
          explanation := "The conservative ledger covers one declared-neighbour scan, the supplied return certificate, three root checks, and one support-membership scan."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowShortThirdIncidence_visibleChecks_le
          ]
        }
      ]
      scopeNotes := "Node [162] classifies only the third incidence at one computed short-return root. Its two constructors feed the separately verified exact consumers [165] and [166]. It performs no support-wide scan, one-return normalization, boundary response construction, D4–D7 reconstruction, CT3 execution, or density argument."
      workBound := "At most 2·n+3+Qbase visible checks. Only one selected root and its supplied bounded support are inspected; no vertex family, graph family, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-non-root-chord-resolution"
      stageId? := some "proof-slice.p13-same-window-non-root-chord-resolution"
      title := "On-return chord resolution"
      plainExplanation := "Equality with node [162]'s computed on-support constructor locates the selected third endpoint at its canonical support index. The resulting literal chord either has target length and closes through the existing CT1 certificate runner, or its rejection supplies the exact strictly shorter return after the same deleted root edge."
      formalStatement := "x_3\\in\\operatorname{supp}(\\Gamma)\\Longrightarrow\\bigl(C_{2^j}\\subseteq G\\bigr)\\;\\lor\\;|\\Gamma'|<|\\Gamma|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-non-root-chord-resolution", title := "On-return chord resolution", nodeIds := [165] },
        { label := "rem:p13-non-root-chord-resolution-scope", title := "Scope of the chord resolution", nodeIds := [165] }
      ]
      declarationGroups := [
        {
          groupId := "p13-chord-resolution-framework"
          title := "Graph-owned literal chord resolver"
          role := .frameworkInterface
          explanation := "The generic resolver consumes exact predecessor equality, scans the supplied support for the canonical endpoint index, constructs the literal chord, and constructs the exact strictly shorter deleted-edge return on rejection."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle_isCycle,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.chordCycle_length,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.shorterReturn,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Input.shorterReturn_strict,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.Result,
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.run
          ]
        },
        {
          groupId := "p13-chord-resolution-provenance"
          title := "Exact computed on-support provenance"
          role := .compositionProvenance
          explanation := "The Erdős input stores equality with node [162]'s computed on-support constructor and passes that same short return to the graph resolver."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
            `Erdos64EG.Internal.P13SameWindowComputedNonRootChord,
            `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.genericInput
          ]
        },
        {
          groupId := "p13-chord-resolution-ct1"
          title := "Existing CT1 target closure"
          role := .tacticExecution
          explanation := "If the constructed chord length is a power of two, the existing certificate-driven CT1 run reaches C1 and contradicts the inherited target-avoidance field."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.targetRun,
            `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.target_terminal,
            `Erdos64EG.Internal.P13SameWindowComputedNonRootChord.target_impossible
          ]
        },
        {
          groupId := "p13-chord-resolution-survivor"
          title := "Exact strictly shorter residual"
          role := .semanticTheorem
          explanation := "After the target constructor is eliminated, the only surviving result retains the rejected literal chord length and the exact graph-owned shorter return with strict length decrease."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowShorterReturn,
            `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution,
            `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution_shorterExact,
            `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution_strict
          ]
        },
        {
          groupId := "p13-chord-resolution-work"
          title := "One bounded support scan"
          role := .workBound
          explanation := "The visible ledger is one scan of the supplied Qbase-bounded support and one target-length decision."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution.visibleChecks_le,
            `Erdos64EG.Internal.p13SameWindowNonRootChordResolution_visibleChecks_le
          ]
        }
      ]
      scopeNotes := "Node [165] proves exactly the CT1 closure of an accepted local chord and, on the surviving branch, the exact strictly shorter deleted-edge return. That residual feeds the verified one-return normalization [167] and packed-support transition [168]. It does not iterate the return, prove termination, or construct the successor/path semantics still white at [170]."
      workBound := "At most Qbase+1 visible checks: one scan of the supplied short support and one power-of-two length decision. No graph, path, cycle, state, response, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-outside-boundary-star"
      stageId? := some "proof-slice.p13-same-window-outside-boundary-star"
      title := "Outside-return cubic boundary-star ownership"
      plainExplanation := "Equality with node [162]'s computed outside constructor fixes one oriented incidence from the literal return support to its selected third endpoint outside. The already certified cubic root gives a three-leaf star, and cubicity proves those three leaves own every incidence at that root."
      formalStatement := "N_G(r)=\\{x_1,x_2,x_3\\},\\qquad r\\in\\operatorname{supp}(\\Gamma),\\quad x_3\\notin\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-outside-boundary-star", title := "Outside-return cubic boundary star", nodeIds := [166] },
        { label := "rem:p13-outside-boundary-star-scope", title := "Scope of the cubic boundary star", nodeIds := [166] }
      ]
      declarationGroups := [
        {
          groupId := "p13-outside-boundary-star-framework"
          title := "Graph-owned oriented cubic star"
          role := .frameworkInterface
          explanation := "The reusable graph layer consumes the exact outside result, retains its support orientation, constructs the cubic star from the certified root divergence, and proves its finite three-leaf shape owns every root incidence."
          declarations := [
            `StructuralExhaustion.Graph.CubicStar.Data,
            `StructuralExhaustion.Graph.CubicStar.Data.SwitchBoundaryShape,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.OrientedReturnBoundary,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.orientedBoundary,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.cubicStar,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.switchBoundaryShape,
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.ownsAllRootIncidences
          ]
        },
        {
          groupId := "p13-outside-boundary-star-provenance"
          title := "Exact computed-outside provenance"
          role := .compositionProvenance
          explanation := "The Erdős input stores equality with node [162]'s computed outside constructor, so the same short residual, return support, selected incidence, and branch context are retained without accepting an independent nonmembership proof."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowShortThirdIncidence,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.graphBranch,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.orientedBoundary,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.root_mem_return_support,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_outside_return_support,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_adjacent_root,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_ne_first_return,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.selected_ne_restored_endpoint
          ]
        },
        {
          groupId := "p13-outside-boundary-star-ownership"
          title := "Exact finite root ownership"
          role := .semanticTheorem
          explanation := "The thin Erdős layer exposes the exact cubic star and switch-boundary shape and proves every ambient incidence at the selected return root is one of its three displayed leaves."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.cubicStar,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.switchBoundaryShape,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.ownsAllRootIncidences
          ]
        },
        {
          groupId := "p13-outside-boundary-star-work"
          title := "Zero additional checks"
          role := .workBound
          explanation := "This node projects proof-carrying node-[162] data; it performs no new primitive scan."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.additionalChecks_eq_zero,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.additionalChecks_eq_zero
          ]
        }
      ]
      scopeNotes := "Node [166] proves only one oriented return-support crossing and exact ownership of the cubic root's three incidences. That residual feeds the verified one-return normalization [167] and packed-support transition [168]. It supplies no all-inside consumer, successor/second stub/path, D4–D7 state, CT3 input, or density estimate."
      workBound := "Zero additional primitive checks beyond node [162]. No support-wide, vertex-family, component, path-family, state, response, or context scan is performed."
    },
    {
      stepId := "erdos.p13-same-window-normalized-return-boundary"
      stageId? := some "proof-slice.p13-same-window-normalized-return-boundary"
      title := "Normalized one-return boundary rejoin"
      plainExplanation := "The exact rejected-chord computation from node [165] and exact outside-boundary computation from node [166] are the only two inputs. The graph normalizer chooses the shorter return and old first step on the chord branch, or the original return and selected third endpoint on the outside branch, while retaining the common cubic root ownership and Qbase bound."
      formalStatement := "|\\Gamma'|\\le |\\Gamma|,\\quad |\\operatorname{supp}(\\Gamma')|\\le Q_{\\rm base},\\quad r x_{\\rm out}\\in E(G),\\quad x_{\\rm out}\\notin\\operatorname{supp}(\\Gamma')"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-normalized-return-boundary", title := "Normalized one-return boundary", nodeIds := [167] },
        { label := "rem:p13-normalized-return-boundary-scope", title := "Scope of the normalized return", nodeIds := [167] }
      ]
      declarationGroups := [
        {
          groupId := "p13-normalized-return-framework"
          title := "Graph-owned two-branch normalization"
          role := .frameworkInterface
          explanation := "The graph layer accepts only complete rejected-chord or outside-boundary predecessor runs, selects one return and one outside incidence, retains the cubic star, and proves the branch-sensitive length and support bounds without scanning."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.RejectedChordRun,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.RejectedChordRun.firstNext_not_mem_shorter_support,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.selectedReturn,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.outsideVertex,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.cubicStar,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.Input.DecreaseEvidence,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.NormalizedReturnBoundary,
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.normalize
          ]
        },
        {
          groupId := "p13-normalized-return-provenance"
          title := "Exact branch-indexed predecessor provenance"
          role := .compositionProvenance
          explanation := "The chord input stores equality with node [165]'s actual runner; the outside input retains node [166]'s exact graph branch. Both are assembled from the same computed node-[162] short residual."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowNonRootChordResolution,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.graphBranch,
            `Erdos64EG.Internal.P13SameWindowComputedShorterBoundary,
            `Erdos64EG.Internal.P13SameWindowComputedShorterBoundary.result_exact,
            `Erdos64EG.Internal.P13SameWindowNormalizedBoundaryInput,
            `Erdos64EG.Internal.P13SameWindowNormalizedBoundaryInput.graphInput
          ]
        },
        {
          groupId := "p13-normalized-return-execution"
          title := "Exact retained boundary facts"
          role := .semanticTheorem
          explanation := "The thin Erdős layer exposes the selected return, one outside adjacent endpoint, exhaustive cubic-root ownership, the inherited Qbase support bound, length at most the original, and strict-versus-equal branch evidence."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowNormalizedReturnBoundary,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_support_bounded,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_length_le,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_outside,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_owns_root,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_rejected_strict,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary_outside_length
          ]
        },
        {
          groupId := "p13-normalized-return-work"
          title := "Zero additional checks"
          role := .workBound
          explanation := "Normalization is a proof transformation over the two computed predecessor packages and performs no primitive finite check."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary.additionalChecks_eq_zero,
            `Erdos64EG.Internal.p13SameWindowNormalizedReturnBoundary_additionalChecks_eq_zero
          ]
        }
      ]
      scopeNotes := "Node [167] is only a proof-level one-return normalization. Its exact output feeds verified packed-support transition [168], whose all-inside branch then feeds verified owner-change node [169]. Node [167] itself supplies no owner table or cross-window token, successor/second stub/component path [170], iteration or termination argument, D4–D7 coordinate, CT3 input, or density theorem."
      workBound := "Zero additional primitive checks. The node selects from proof-carrying predecessor data and does not scan a support, vertex set, component family, state family, response family, or context family."
    },
    {
      stepId := "erdos.p13-same-window-packed-support-transition"
      stageId? := some "proof-slice.p13-same-window-packed-support-transition"
      title := "Normalized-return packed-support transition"
      plainExplanation := "Equality with node [167]'s computed normalized result fixes one ambient simple return ending in a selected ambient-cubic window support. A graph-owned ordered edge scan either proves every return-support vertex lies in the union of all ambient-cubic selected-window supports, or returns the first membership transition with its oriented crossing, exact BoundaryStub, outside endpoint, and induced-remainder component."
      formalStatement := "\\operatorname{supp}(\\Gamma')\\subseteq U_{\\rm ac}\\quad\\lor\\quad\\exists\\text{ first }uv:\\quad u\\in U_{\\rm ac},\\quad v\\notin U_{\\rm ac}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-packed-support-transition", title := "Normalized-return packed-support transition", nodeIds := [168] },
        { label := "rem:p13-packed-support-transition-scope", title := "Scope of the packed-support transition", nodeIds := [168] }
      ]
      declarationGroups := [
        {
          groupId := "p13-packed-support-transition-framework"
          title := "Graph-owned first membership transition"
          role := .frameworkInterface
          explanation := "The generic graph layer scans the edge indices of one supplied path against the union of all ambient-cubic selected-window supports. Absence propagates final membership across the whole support; a first hit is oriented inside-to-outside and converted to an exact BoundaryStub and induced-remainder component."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.Inside,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.TransitionAt,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.scan,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Input.support_subset_of_no_transition,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.ofFirstHit,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.windowPosition,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.outside_mem_externalNeighbors,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.OrientedCrossing.boundaryStub,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.Result,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.run
          ]
        },
        {
          groupId := "p13-packed-support-transition-provenance"
          title := "Exact node-[167] return provenance"
          role := .compositionProvenance
          explanation := "The Erdős input stores equality with node [167]'s computed result, preserves its Qbase-bounded return as one ambient simple path, and proves its selected-window endpoint belongs to the ambient-cubic support union."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnBoundary,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.support_bounded,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.ambientPath,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.ambientPath_isPath,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.endpoint_mem_deletedWindowVertices,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput_path_length,
            `Erdos64EG.Internal.P13SameWindowComputedNormalizedReturnBoundary.graphInput_length_le_Qbase
          ]
        },
        {
          groupId := "p13-packed-support-transition-execution"
          title := "Exact exhaustive packed-support dichotomy"
          role := .semanticTheorem
          explanation := "The thin Erdős layer exposes exactly full support containment or the first transition package, including the literal stub, endpoint, and component produced by the graph runner."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowNormalizedReturnPackedSupportTransition,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition_exhaustive
          ]
        },
        {
          groupId := "p13-packed-support-transition-work"
          title := "Exact local work and polynomial bound"
          role := .workBound
          explanation := "The ledger computes thirteen degree tests and cubic flags for each selected window, then performs two finite packed-support membership scans per edge of the one supplied return."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks_eq,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonBoundaryTransition.visibleChecks_le_square_add_linear,
            `Erdos64EG.Internal.p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_eq,
            `Erdos64EG.Internal.p13SameWindowNormalizedReturnPackedSupportTransition_visibleChecks_le
          ]
        }
      ]
      scopeNotes := "The union is over all ambient-cubic selected windows, not the manuscript's selected cold subfamily. Its all-inside branch feeds verified owner-change node [169], while its exact first-transition branch feeds verified component boundary schedule [170]. No aggregate cold mass, iteration, D4–D7 statement, CT3 execution, or density estimate follows."
      workBound := "Exactly 13pn+13p+26pL visible checks, where p is the selected-window packing number and L is the one supplied return length; at most n²+(2Qbase+1)n. No graph, path, coloring, state, response, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-boundary-schedule"
      stageId? := some "proof-slice.p13-same-window-component-boundary-schedule"
      title := "Component boundary schedule and BFS path"
      plainExplanation := "Equality with node [168]'s computed first-transition result fixes the exact boundary stub and returned outside component. The same computed outside BFS finset drives a proof-carrying exit scan, the explicit finite window-slot search, the complete incident-stub schedule, its true cyclic successor, and the declared-order shortest BFS path between the two retained boundary neighbours."
      formalStatement := "s^+(b)\\ne b,\\quad C(s^+(b))=C(b),\\quad P_C(b,s^+(b))\\text{ is a shortest declared-order BFS path}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-boundary-schedule", title := "Component boundary schedule and BFS path", nodeIds := [170] },
        { label := "rem:p13-component-boundary-schedule-scope", title := "Scope of the component boundary schedule", nodeIds := [170] }
      ]
      declarationGroups := [
        {
          groupId := "p13-component-boundary-framework"
          title := "Shared computed component, first exits, and cyclic schedule"
          role := .frameworkInterface
          explanation := "The reusable graph package computes one outside BFS component and reuses it literally for the first exit certificate, explicit WindowIndex × Fin 13 first hit, distinct second stub, complete duplicate-free incident schedule, fixed-point-free List.next successor, and ordered-BFS shortest path."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.outsideBfsProfile,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentVertices,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.mem_componentVertices_iff,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.exitCertificate,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.windowPosition_firstHit,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.secondStub,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.Input.second_distinct,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.incidentStubs,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.mem_incidentStubs_iff,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.two_le_incidentStubs_length,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.successor,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.successor_distinct,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.twoStubComponent,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath_isPath,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.componentPath_shortest
          ]
        },
        {
          groupId := "p13-component-boundary-provenance"
          title := "Exact node-[168] first-transition provenance"
          role := .compositionProvenance
          explanation := "The thin Erdős adapter retains the actual node-[168] run, exact first-transition stub, outside endpoint, and returned component; it supplies only the inherited nonbridge fact needed for the second return."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.graphInput,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.result,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.anchor_is_exact_node168_stub,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.computed_exit_and_schedule,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.successor_distinct_and_same_returned_component,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.successor_is_stored_cyclic_next,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.slot_first_hit_provenance,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath_shortest
          ]
        },
        {
          groupId := "p13-component-boundary-work"
          title := "Complete visible ledger and cubic bound"
          role := .workBound
          explanation := "The exact ledger includes the return scan, explicit slot first-hit search, both BFS computations, incident-token filtering, and component-object restriction; each BFS budget is separately polynomial."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.visibleChecks_eq,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.bfsBudget_polynomial,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.outsideBfsBudget_polynomial,
            `StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule.visibleChecks_polynomial,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.visibleChecks_eq,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.visibleChecks_polynomial
          ]
        }
      ]
      scopeNotes := "Node [170] belongs only to node [161]'s short first-transition branch and feeds verified one-state component observation [173]. That branch is incompatible with the verified long node-[163]--[164] branch and its white full-semantic consumer [179]; there is no edge from this short branch to [164] or [179]. Node [170] supplies no D4–D7 label, repetition, Boolean or cold-family semantics, iteration, target closure, CT3 execution, or density estimate."
      workBound := "The visible ledger includes 13p slot checks, L·|C| exit-component lookups, both explicit BFS budgets, |C|² component restriction, token filtering, and the declared-order component BFS; it is at most 50·localScale³."
    },
    {
      stepId := "erdos.p13-same-window-component-d1d3-observation"
      stageId? := some "proof-slice.p13-same-window-component-d1d3-observation"
      title := "One component D1--D3 observation"
      plainExplanation := "Node [173] consumes node [170]'s exact two-boundary component schedule and independently computes its declared-order BFS-tree shortest path. Equality to that one computed path gives the observation interface's rank; no path family is ordered or scanned. The two literal degrees, two Fin 13 offsets, and connector length form one genuine State (Fin 0), while the empty local response honestly retains MissingD4D7 reconstruction."
      formalStatement := "s_C\\in\\operatorname{State}(\\operatorname{Fin}(0)),\\qquad \\operatorname{MissingD4D7}(s_C)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d1d3-observation", title := "One component D1--D3 observation", nodeIds := [173] },
        { label := "rem:p13-component-d1d3-observation-scope", title := "Scope of the component D1--D3 observation", nodeIds := [173] }
      ]
      declarationGroups := [
        {
          groupId := "p13-component-d1d3-framework"
          title := "Computed-path observation and genuine empty-coordinate state"
          role := .frameworkInterface
          explanation := "The graph package independently computes the declared-order BFS-tree shortest path and ranks a supplied candidate only by equality with that computed path. It then materializes the two boundary observations, projects the unique Fin 0 local response, and exposes MissingD4D7 rather than inventing later coordinates."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.data,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.bfsPathTieBreak,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.canonicalPath,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.observations,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.emptyLocalProjection,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.state,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.OneStateResidual,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.run,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.boundaryDegree_zero,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.boundaryDegree_one,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.windowOffset_zero,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.windowOffset_one,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.targetResponse_eq,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.localResponse_empty
          ]
        },
        {
          groupId := "p13-component-d1d3-provenance"
          title := "Exact node-[170] schedule and independently computed path"
          role := .compositionProvenance
          explanation := "The adapter consumes node [170]'s actual result and graph input. Its connector is the independently computed declared-order BFS-tree shortest path, and equality with that value is used only to package the existing observation rank."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.result,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.componentPath_shortest,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_exact_node170_data
          ]
        },
        {
          groupId := "p13-component-d1d3-execution"
          title := "One exact State (Fin 0) and MissingD4D7 residual"
          role := .semanticTheorem
          explanation := "The thin Erdős execution uses PowerOfTwoLength for the thirteen fixed target offsets, proves equality with the exact projected state, and returns the genuine missing-reconstruction residual."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowComponentD1D3Residual,
            `Erdos64EG.Internal.runP13SameWindowComponentD1D3Observation,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_exact_state,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_missing_d4_d7,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_targetResponse
          ]
        },
        {
          groupId := "p13-component-d1d3-work"
          title := "Exact local work and linear bound"
          role := .workBound
          explanation := "Materializing this single state reads two degree rows and thirteen fixed target offsets; the stored path length, offsets, and empty local response introduce no ambient or path-family scan."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.visibleChecks_eq,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Observation.visibleChecks_linear,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_visibleChecks_eq,
            `Erdos64EG.Internal.p13SameWindowComponentD1D3_visibleChecks_linear
          ]
        }
      ]
      scopeNotes := "Node [173] constructs one state only. Its MissingD4D7 residual feeds the verified cyclic component D1–D3 ledger split [174], which in turn feeds the white D4–D7 reconstruction/coarse-repeat consumer [175]. Neither edge enters long-branch node [164] or [179]. Node [173] itself proves no state sequence, repetition, D4–D7 reconstruction, CT3 compression, Boolean or cold-family semantics, target closure, or density estimate."
      workBound := "Exactly 2n+13 visible checks and at most 15(n+1). The independently computed BFS path is inherited from node [170]; no path family is generated, ordered, or scanned."
    },
    {
      stepId := "erdos.p13-same-window-component-d1d3-ledger"
      stageId? := some "proof-slice.p13-same-window-component-d1d3-ledger"
      title := "Cyclic component D1--D3 ledger split"
      plainExplanation := "Node [174] requires the exact typed node-[173] residual and retains its state as the anchor row. It traverses node [170]'s complete incident-stub schedule with the stored true cyclic successor and computes one local D1--D3 row per scheduled stub. A finite collision search over only those observed rows returns either two distinct rows with the same coarse state or a proof that the schedule has length at most Qbase."
      formalStatement := "(\\exists i\\ne j,\\ s_i=s_j)\\ \\lor\\ |\\mathcal S_C|\\le Q_{\\rm base}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d1d3-ledger", title := "Cyclic component D1--D3 ledger split", nodeIds := [174] },
        { label := "rem:p13-component-d1d3-ledger-scope", title := "Scope of the cyclic D1--D3 ledger", nodeIds := [174] }
      ]
      declarationGroups := [
        {
          groupId := "p13-component-d1d3-ledger-framework"
          title := "Observed-row cyclic ledger and finite collision"
          role := .frameworkInterface
          explanation := "The reusable graph layer re-anchors the exact local two-boundary schedule, uses List.next for the cyclic successor, materializes only scheduled observation rows, and applies finite code collision to their exact coarse states."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Input,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.stubs,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.connector_successor_eq,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rowState,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rowState_anchor,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.rows,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.stateCard,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Repetition,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.Result,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.run
          ]
        },
        {
          groupId := "p13-component-d1d3-ledger-provenance"
          title := "Exact node-[173] anchor and node-[170] schedule"
          role := .compositionProvenance
          explanation := "The source type stores node [173]'s residual and equality to its actual run. The anchor row is projected from that retained value, while every other row is computed from node [170]'s exact complete incident schedule."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowComponentD1D3LedgerSource,
            `Erdos64EG.Internal.P13SameWindowComponentD1D3LedgerSource.node173Exact,
            `Erdos64EG.Internal.computedP13SameWindowComponentD1D3LedgerSource,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_exact_node170_schedule,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_source_exact_node173,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_true_cyclic_successor,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_anchor_row_eq_retained,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_retained_anchor_agrees_actual_node173
          ]
        },
        {
          groupId := "p13-component-d1d3-ledger-execution"
          title := "Exhaustive repetition-or-bounded split"
          role := .semanticTheorem
          explanation := "The thin Erdős adapter runs the observed-row classifier and rewrites the exact state-cardinality bound to Qbase. Both constructors are retained for the still-open node-[175] consumer."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.D1D3LedgerRepetition,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.D1D3LedgerOutput,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD1D3Ledger,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD1D3Ledger_exhaustive
          ]
        },
        {
          groupId := "p13-component-d1d3-ledger-work"
          title := "Local schedule/BFS work only"
          role := .workBound
          explanation := "The ledger scans the actual incident schedule and its local connector/BFS clauses. It never enumerates the State universe; Qbase enters only through the proved cardinality of the coarse code."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.visibleChecks,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.localScale,
            `StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger.visibleChecks_polynomial,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d1d3Ledger_visibleChecks_polynomial
          ]
        }
      ]
      scopeNotes := "Node [174] proves only the local exhaustive split. Its repeated branch records equality of two observed coarse D1--D3 states but does not prove full response equivalence or CT3 removability; its bounded branch proves only schedule length at most Qbase. The D4--D7 reconstruction or coarse-repeat consumer remains white node [175]. No edge enters long-branch node [164] or [179], and no ambient State universe is enumerated."
      workBound := "At most 100·localScale^4 visible checks over the exact incident schedule and local BFS clauses. The Qbase state-cardinality equality is proof-only."
    },
    {
      stepId := "erdos.p13-same-window-component-d4d7-classifier"
      stageId? := some "proof-slice.p13-same-window-component-d4d7-classifier"
      title := "D4--D7 availability and coarse-repeat routing"
      plainExplanation := "Node [175] consumes the exact node-[174] result. A repeated coarse row pair is passed unchanged to a promoted CT10 refinement; a bounded schedule scans only its stored rows and returns a complete D4--D7 family or its first typed missing row, which is also routed through CT10 on the actual branch context."
      formalStatement := "\\text{node-[174] result}\\Longrightarrow\\text{routed coarse repeat, reconstructed rows, or routed first missing row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d4d7-classifier", title := "D4--D7 availability and coarse-repeat classifier", nodeIds := [175] },
        { label := "rem:p13-component-d4d7-classifier-scope", title := "Scope of the D4--D7 classifier", nodeIds := [175] }
      ]
      declarationGroups := [{
        groupId := "p13-component-d4d7-classifier-total"
        title := "Exact node-174 consumer, two CT10 routes, and local work"
        role := .semanticTheorem
        explanation := "The graph runner consumes only node [174]'s observed split. Both generic CT10 routes preserve the actual context and promote an explicit retained row; the thin P13 adapter proves generic and specialized predecessor equality and the combined local work bound."
        declarations := [
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7OrCoarseRepeat_exhaustive,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.run,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.run_exhaustive,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7OrCoarseRepeat.visibleChecks_polynomial,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseExecution,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_terminal_promoted,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarse_trace_valid,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingExecution,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missing_trace_valid,
          `Erdos64EG.Internal.computedP13SameWindowComponentD4D7OrCoarseRepeatSource,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7OrCoarseRepeat,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_generic_node174,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_exact_specialized_node174,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7Consumer_totalVisibleChecks_polynomial,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseRouteContract,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingRouteContract
        ]
      }]
      scopeNotes := "Node [175] classifies only the availability of graph-derived D4--D7 clauses and retains exact refinement residuals. It proves no full D4--D7 compatible-response equivalence, CT8 removal, certified smaller object, second connector, cycle, or target closure; those implications remain white node [180]."
      workBound := "At most 3·localScale primitive checks over the actual incident schedule and two retained CT10 inputs. The State, response, context, graph, and universe families are never enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-d4d7-semantics"
      stageId? := some "proof-slice.p13-same-window-component-d4d7-readiness"
      title := "Component D4--D7 semantic readiness"
      plainExplanation := "Node [180] consumes node [175]'s exact execution. The complete-reconstruction constructor is impossible at the retained anchor row; the surviving coarse and bounded constructors preserve their CT10 objects and explicit missing D4--D7 witnesses."
      formalStatement := "\\text{node-[175] execution}\\Longrightarrow\\text{coarse missing pair or bounded first-missing row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d4d7-semantic-readiness", title := "Component D4--D7 semantic readiness", nodeIds := [180] }
      ]
      declarationGroups := [{
        groupId := "p13-component-d4d7-readiness-total"
        title := "Exact node-[175] residual and local constructor elimination"
        role := .semanticTheorem
        explanation := "The graph theorem proves anchor membership and eliminates the impossible reconstructed constructor. The Erdős adapter exposes exact predecessor equality, the exhaustive two-way residual, and its one-check work bound."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.anchor_mem_stubs,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.reconstructed_impossible,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.run,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.run_exhaustive,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.source_exact,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness.visibleChecks_linear,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.computedD4D7SemanticReadinessSource,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7SemanticReadiness_exact_node175,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7SemanticReadiness,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7SemanticReadiness_exhaustive,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7SemanticReadiness_visibleChecks_polynomial,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7SemanticReadinessPrefix
        ]
      }]
      scopeNotes := "Node [180] proves readiness only. It does not construct compatible-response equivalence, a remove operation, a smaller object, or CT8 execution; those remain white node [182]."
      workBound := "One predecessor-constructor inspection, bounded by localScale+1. No response, context, state, graph, or universe family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-ct8-consumer"
      stageId? := some "proof-slice.p13-component-d4d7-clause-schedule"
      title := "Fixed D4--D7 clause schedule"
      plainExplanation := "Node [182] retains every exact node-[180] missing marker and assigns only the fixed noduplicated D4,D5,D6,D7 obligation order. It deliberately asserts no clause truth."
      formalStatement := "\\text{node-[180] marker}\\Longrightarrow[D4,D5,D6,D7]\\text{ obligation ledger}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4d7-clause-schedule", title := "Fixed D4--D7 clause schedule", nodeIds := [182] }]
      declarationGroups := [{
        groupId := "p13-d4d7-clause-schedule-total"
        title := "Exact markers, fixed schedule, and actual emitted-slot bound"
        role := .semanticTheorem
        explanation := "The graph layer constructs a four-slot ledger from each retained marker. The application proves exact node-[180] equality, exhaustiveness, and that the computed output emits eight slots on the coarse branch or four on the bounded branch."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.clauseOrder_nodup,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.run,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.run_total,
          `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule.emittedSlots_le_eight,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseSchedule_exact_node180,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseSchedule_exhaustive,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseSchedule_emittedSlots_le_eight,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseSchedulePrefix
        ]
      }]
      scopeNotes := "Node [182] schedules obligations only. It proves no clause predicate, response equivalence, removal, smaller object, or CT8 execution; those remain white node [185]."
      workBound := "At most eight actual emitted slots; ambient universes are not inspected."
    },
    {
      stepId := "erdos.p13-component-d4d7-semantic-consumer"
      stageId? := some "proof-slice.p13-component-d4d7-clause-cursor"
      title := "D4 obligation cursor"
      plainExplanation := "Node [185] consumes node [182]'s exact ledgers, focuses D4 as the next obligation, and retains D5--D7 as an exact unevaluated tail."
      formalStatement := "[D4,D5,D6,D7]\\Longrightarrow D4\\ \\text{ focused with tail }[D5,D6,D7]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4d7-clause-cursor", title := "D4 obligation cursor", nodeIds := [185] }]
      declarationGroups := [{
        groupId := "p13-d4d7-cursor"
        title := "Exact cursor and tail"
        role := .semanticTheorem
        explanation := "The dependent cursor preserves markers and proves the actual remaining-slot bound."
        declarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.run_total,
        `StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor.remainingSlots_le_six,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseCursor_exact_node182,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseCursor_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4D7ClauseCursor_remainingSlots_le_six,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4D7ClauseCursorPrefix
      ] }]
      scopeNotes := "Node [185] asserts no D4 truth or response/CT8 semantics; those remain white node [188]."
      workBound := "At most six retained tail slots."
    },
    {
      stepId := "erdos.p13-component-d4d7-d4-consumer"
      stageId? := some "proof-slice.p13-component-d4-local-clause-request"
      title := "Graph-derived D4 evaluation request"
      plainExplanation := "Node [188] preserves node [185]'s exact dependent cursor and emits a singleton request for the actual D4 head while retaining D5--D7 unchanged."
      formalStatement := "D4::[D5,D6,D7]\\Longrightarrow\\text{request }[D4]\\text{ with tail }[D5,D6,D7]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-local-clause-request", title := "Local D4 evaluation request", nodeIds := [188] }]
      declarationGroups := [{
        groupId := "p13-d4-local-request"
        title := "Exact dependent D4 requests"
        role := .semanticTheorem
        explanation := "The framework request stores only the actual cursor, singleton D4 slot, and exact tail. The application proves exact node-[185] provenance, exhaustiveness, and two actual requests on the coarse branch or one on the bounded branch."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.request,
          `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.run,
          `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.run_total,
          `StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest.requestedSlots_le_two,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4LocalClauseRequest_exact_node185,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4LocalClauseRequest_exhaustive,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4LocalClauseRequest_requestedSlots_le_two,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4LocalClauseRequestPrefix
        ]
      }]
      scopeNotes := "Node [188] supplies no predicate, truth value, response equivalence, or CT8 result; graph-derived semantics remain white node [191]."
      workBound := "At most two actual singleton request slots; no ambient universe is enumerated."
    },
    {
      stepId := "erdos.p13-component-d4-semantics"
      stageId? := some "proof-slice.p13-component-d4-evaluator-residual"
      title := "D4 evaluator residual"
      plainExplanation := "Node [191] preserves every exact node [188] request and exposes the missing graph-local predicate and provenance requirements without accepting an evaluator."
      formalStatement := "\\text{D4 request}\\Longrightarrow[\\text{graph-local predicate},\\text{provenance}]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-evaluator-residual", title := "D4 evaluator residual", nodeIds := [191] }]
      declarationGroups := [{
        groupId := "p13-d4-evaluator-residual"
        title := "Exact evaluator requirements"
        role := .semanticTheorem
        explanation := "Each residual retains its request, marker, and tail and records exactly the two missing evaluator requirements."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.residual,
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.run,
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.run_total,
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual.requiredInputs_le_four,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4EvaluatorResidual_exact_node188,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorResidual_exhaustive,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorResidual_requiredInputs_le_four,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorResidualPrefix
        ]
      }]
      scopeNotes := "No Boolean, predicate, evaluator, response equivalence, or CT8 result is supplied; node [194] records the terminal construction residual."
      workBound := "At most four actual requirement tags."
    },
    {
      stepId := "erdos.p13-component-d4-evaluator-producer"
      stageId? := some "proof-slice.p13-component-d4-evaluator-construction-residual"
      title := "Graph-owned D4 evaluator construction residual"
      plainExplanation := "Node [194] preserves every exact node-[191] request, marker, and D5--D7 tail and records the three graph-owned inputs still needed to construct the D4 evaluator."
      formalStatement := "\\text{node-[191] residual}\\Longrightarrow[\\text{component data},\\text{predicate definition},\\text{derivation}]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-evaluator-construction-residual", title := "D4 evaluator construction residual", nodeIds := [194] }]
      declarationGroups := [{
        groupId := "p13-d4-evaluator-construction-residual"
        title := "Exact graph-owned construction requirements"
        role := .semanticTheorem
        explanation := "The graph layer retains node [191] exactly and appends only the ordered construction tags; the application proves the coarse and bounded leaves exhaustively."
        declarations := [
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual.residual,
          `StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorConstructionResidual.constructionInputs,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorConstruction_exhaustive,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4EvaluatorConstruction_requiredInputs_le_six,
          `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exists_verifiedD4EvaluatorConstructionPrefix
        ]
      }]
      scopeNotes := "This terminal interface supplies no predicate, evaluator, truth value, response equivalence, or CT8 result. No caller Boolean is accepted."
      workBound := "At most six fixed local requirement tags; no ambient universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-packed-owner-change"
      stageId? := some "proof-slice.p13-same-window-packed-owner-change"
      title := "Ambient-cubic owner sequence and first cross-window edge"
      plainExplanation := "Equality with node [168]'s all-inside result fixes the same normalized return. A once-prepared finite inventory assigns and stores the unique ambient-cubic selected-window owner of every return vertex. The single-window result contradicts the original external stub neighbour, so the surviving result is the first owner-change edge with two exact opposite cross-window tokens."
      formalStatement := "\\exists i<|\\Gamma'|:\\quad W_i\\ne W_{i+1}\\quad\\text{and two exact cross-window tokens}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-packed-owner-change", title := "First ambient-cubic owner change", nodeIds := [169] },
        { label := "rem:p13-packed-owner-change-scope", title := "Scope of the owner change", nodeIds := [169] }
      ]
      declarationGroups := [
        {
          groupId := "p13-packed-owner-framework"
          title := "Stored unique owner table and first change"
          role := .frameworkInterface
          explanation := "The graph layer prepares the finite ambient-cubic slot inventory, performs one finite lookup per path vertex, stores the resulting owner table, scans adjacent stored owners, and packages the first difference with two exact cross-window tokens."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.OwnedSlot,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.OwnedSlot.window_unique,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.lookup,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.OwnerTable,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.prepareOwnerTable,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Input.OwnerChangeAt,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.FirstCrossWindow,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.FirstCrossWindow.ofFirstHit,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.Result,
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.run
          ]
        },
        {
          groupId := "p13-packed-owner-provenance"
          title := "Exact all-inside provenance"
          role := .compositionProvenance
          explanation := "The input stores equality with node [168]'s computed all-inside constructor and passes that same Qbase-bounded path and containment proof into the generic owner preparation."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowNormalizedReturnPackedSupportTransition,
            `Erdos64EG.Internal.P13SameWindowComputedAllInside,
            `Erdos64EG.Internal.P13SameWindowComputedAllInside.graphInput,
            `Erdos64EG.Internal.P13SameWindowComputedAllInside.graphInput_support_bounded
          ]
        },
        {
          groupId := "p13-packed-owner-execution"
          title := "Exact surviving first cross-window edge"
          role := .semanticTheorem
          explanation := "The selected stub neighbour excludes the single-window result. The thin Erdős output retains the stored owner table, first hit, crossing, and both exact cross-window token fields."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowFirstCrossWindow,
            `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange,
            `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange_exact
          ]
        },
        {
          groupId := "p13-packed-owner-work"
          title := "Stored-table local work"
          role := .workBound
          explanation := "The once-prepared inventory and owner table are scanned locally; subsequent edge comparisons use stored entries."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathColdSkeletonOwnerChange.visibleChecks_le,
            `Erdos64EG.Internal.p13SameWindowPackedOwnerChange_visibleChecks_le
          ]
        }
      ]
      scopeNotes := "Owners range over all ambient-cubic selected windows, not the manuscript cold subfamily. Its exact first-cross-window package feeds verified zero-check handoff node [171]. Node [169] constructs no boundary successor, target-cycle closure, cold aggregate, D4–D7 coordinate, CT3 input, or density estimate."
      workBound := "At most n²+Qbase(n+1) visible checks using one prepared slot inventory, one stored owner lookup per path vertex, and one stored-owner comparison per edge."
    },
    {
      stepId := "erdos.p13-same-window-cross-window-token-pair"
      stageId? := some "proof-slice.p13-same-window-cross-window-token-pair"
      title := "Exact cross-window token-pair residual"
      plainExplanation := "Node [171] consumes node [169]'s complete first-cross-window package. A reusable typed route projects the two already computed endpoint tokens, proves they are distinct opposite oriented contributions of the same literal edge, and retains both exact cross-window subtypes without performing another search. This is the terminal residual of the computed all-inside branch."
      formalStatement := "t_L\\ne t_R\\quad\\land\\quad \\operatorname{subtype}(t_L)=\\operatorname{subtype}(t_R)=\\mathtt{crossWindow}\\quad\\land\\quad e(t_L)=e(t_R)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-cross-window-token-pair", title := "Exact cross-window token-pair residual", nodeIds := [171] },
        { label := "rem:p13-cross-window-token-pair-scope", title := "Scope of the token-pair residual", nodeIds := [171] }
      ]
      declarationGroups := [
        {
          groupId := "p13-cross-window-token-pair-route"
          title := "Typed zero-check route"
          role := .frameworkInterface
          explanation := "The reusable route projects both exact tokens, endpoint windows, positions, and vertices from one FirstCrossWindow package, proves the tokens distinct, and records their opposite orientations on the same Sym2 edge."
          declarations := [
            `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.CrossWindowTokenPair,
            `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.route,
            `StructuralExhaustion.Routes.InducedPathCrossWindowTokenPair.additionalChecks_eq_zero
          ]
        },
        {
          groupId := "p13-cross-window-token-pair-provenance"
          title := "Exact node-169 provenance"
          role := .compositionProvenance
          explanation := "The input is the complete computed node-[169] first-cross-window residual, including its stored table, first hit, crossing, and exact run equality."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowFirstCrossWindow,
            `Erdos64EG.Internal.runP13SameWindowPackedOwnerChange_exact
          ]
        },
        {
          groupId := "p13-cross-window-token-pair-execution"
          title := "Thin exact residual"
          role := .semanticTheorem
          explanation := "The Erdős adapter invokes only the generic route and exposes exact equality with both source tokens."
          declarations := [
            `Erdos64EG.Internal.P13SameWindowCrossWindowTokenPair,
            `Erdos64EG.Internal.runP13SameWindowCrossWindowTokenPair,
            `Erdos64EG.Internal.runP13SameWindowCrossWindowTokenPair_source_exact
          ]
        },
        {
          groupId := "p13-cross-window-token-pair-work"
          title := "Zero additional checks"
          role := .workBound
          explanation := "All fields are proof-carrying projections from node [169]; the residual adds no primitive predicate evaluation."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowCrossWindowTokenPair_additionalChecks_eq_zero
          ]
        }
      ]
      scopeNotes := "Node [171] is the exact terminal residual of the computed all-inside branch. It proves no second connector, repeated-owner structure, cycle, cold-family membership, demand or capacity bound, successor, target closure, CT execution, or density estimate."
      workBound := "Exactly zero additional primitive checks after node [169]; no graph, path, connector, cycle, state, demand, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-support-prefix"
      stageId? := some "proof-slice.p13-same-window-long-support-prefix"
      title := "Exact long-support forced prefix"
      plainExplanation := "Equality with node [161]'s computed long constructor retains Qbase below the literal support length on the identical branch context. The generic handoff embeds the first Qbase+1 positions, identifies Qbase as the unique overflow index, and classifies any supplied support position as inside that prefix or after it."
      formalStatement := "Q_{\\rm base}<|\\operatorname{supp}(\\Gamma)|\\Longrightarrow\\{0,\\ldots,Q_{\\rm base}\\}\\hookrightarrow\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-support-prefix", title := "Forced long-support prefix", nodeIds := [163] },
        { label := "rem:p13-long-support-prefix-scope", title := "Scope of the long prefix", nodeIds := [163] }
      ]
      declarationGroups := [
        {
          groupId := "p13-long-prefix-framework-route"
          title := "Generic finite-support handoff"
          role := .frameworkInterface
          explanation := "The route preserves the dependent branch context, enumerates only literal support and prefix positions, embeds the forced prefix, and provides one-comparison local classifiers."
          declarations := [
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.Source,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.Residual,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.prefixPositions_card,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.prefixEmbedding,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.overflowImage_val,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.classifyPrefixPosition,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.classifyPosition,
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.route
          ]
        },
        {
          groupId := "p13-long-prefix-provenance"
          title := "Exact computed-long source"
          role := .compositionProvenance
          explanation := "The input stores equality with node [161]'s long result. The thin source and result retain the literal corridor length, exact Qbase scale, strict inequality, and identical ambient graph."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowBaseScaleSplit,
            `Erdos64EG.Internal.P13SameWindowLongOutput,
            `Erdos64EG.Internal.p13SameWindowLongSource,
            `Erdos64EG.Internal.P13SameWindowLongSupportPrefix,
            `Erdos64EG.Internal.runP13SameWindowLongSupportPrefix,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_exact_length,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_exact_scale,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_ambient_preserved
          ]
        },
        {
          groupId := "p13-long-prefix-audits"
          title := "Prefix cardinality and local classifications"
          role := .executionAudit
          explanation := "The forced prefix has exactly Qbase+1 positions, the unique overflow image is Qbase, and both prefix positions and arbitrary supplied support positions have exhaustive exact classifiers."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_card,
            `Erdos64EG.Internal.p13SameWindowLongSupportOverflowImage_val,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClass_exhaustive,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefix_overflow_iff,
            `Erdos64EG.Internal.p13SameWindowLongSupportPositionClass_exhaustive
          ]
        },
        {
          groupId := "p13-long-prefix-work"
          title := "Constant local work ledger"
          role := .workBound
          explanation := "Constructing the inclusion performs no scan. Classifying one supplied prefix or support position uses one natural-number comparison."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefixChecks,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefixChecks_eq_zero,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClassifierChecks,
            `Erdos64EG.Internal.p13SameWindowLongSupportPrefixClassifierChecks_eq_one
          ]
        }
      ]
      scopeNotes := "Node [163] provides only literal finite positions and exact inclusions. It assigns no normalized state labels and supplies no D4–D7 response, CT17 target/offset/compatibility semantics, or density estimate. Its exact prefix feeds verified first-nine classifier [164]."
      workBound := "Zero scans to construct the forced prefix; one natural-number comparison for each supplied position classification. No support family, state universe, graph family, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-state-labels"
      stageId? := some "proof-slice.p13-same-window-long-prefix-state-labels"
      title := "First-nine coarse-label collision and CT10 refinement"
      plainExplanation := "Node [164] consumes node [163]'s actual run, maps only its first nine exact positions to the literal corridor, computes the graph-derived degree-modulo-four and selected-packing-membership label, retains a collision in the eight-label alphabet, and promotes the missing compatible-response layer through CT10."
      formalStatement := "\\exists i\\ne j<9,\\ (d_G(v_i)\\bmod 4,\\mathbf 1_{v_i\\in V(\\mathcal P_{13})})=(d_G(v_j)\\bmod 4,\\mathbf 1_{v_j\\in V(\\mathcal P_{13})})"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-prefix-observed-label", title := "First-nine observed-label refinement", nodeIds := [164] },
        { label := "rem:p13-long-prefix-observed-label-scope", title := "Scope of first-nine refinement", nodeIds := [164] }
      ]
      declarationGroups := [{
        groupId := "p13-long-prefix-observed-label-total"
        title := "Exact local collision, route, CT10 trace, and work"
        role := .semanticTheorem
        explanation := "The graph layer scans only nine actual occurrences; the route preserves node [163]'s exact source and gives CT10 precisely the two collided positions. The exhaustive trace promotes responseContexts, while the work ledger remains linear in the local graph size."
        declarations := [
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_terminal,
          `StructuralExhaustion.Graph.LongPrefixObservedLabel.Input,
          `StructuralExhaustion.Graph.LongPrefixObservedLabel.labels_card,
          `StructuralExhaustion.Graph.LongPrefixObservedLabel.run,
          `StructuralExhaustion.Graph.LongPrefixObservedLabel.run_decision_exact,
          `StructuralExhaustion.Graph.LongPrefixObservedLabel.visibleChecks_le,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticCapability,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticInput_values,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_first_missing_responseContexts,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_trace,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_verified,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_trace_valid,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semantic_run_total,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.semanticChecks_eq_nine,
          `Erdos64EG.Internal.P13SameWindowLongPrefixStateSource,
          `Erdos64EG.Internal.p13SameWindowLongPrefixStateSource,
          `Erdos64EG.Internal.p13SameWindowLongPrefixFirstNineEmbedding,
          `Erdos64EG.Internal.P13SameWindowLongPrefixStateLabels,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_distinct,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_sameCoarseLabel,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_trace,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_verified,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_trace_valid,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ct10_total,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_totalVisibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixStateLabels_ambient_preserved,
          `StructuralExhaustion.Routes.LongPrefixObservedLabel.route,
          `Erdos64EG.Internal.P13SameWindowLongPrefixStateSource.node163Exact,
          `Erdos64EG.Internal.p13SameWindowLongPrefixStateSource_exactNode163,
          `Erdos64EG.Internal.p13SameWindowLongPrefixObservedVertex_exact
        ]
      }]
      scopeNotes := "Node [164] proves only equality of one graph-derived coarse label at two distinct literal first-nine occurrences. Node [179] refines their full degrees; D4–D7 response equivalence, CT8 removal, and a certified smaller object remain white node [183]."
      workBound := "At most 144(|V|+1)+9 primitive checks: the fixed first-nine collision scan plus the three-class CT10 scan on two retained occurrences. No ambient label, response, context, state, graph, or universe family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-full-semantics"
      stageId? := some "proof-slice.p13-same-window-long-prefix-degree-refinement"
      title := "Two-occurrence exact degree refinement"
      plainExplanation := "Node [179] retains node [164]'s actual collided pair and promoted CT10 response-context obligation, reads only the two literal corridor degree rows, and returns equal full degrees or a nonzero degree gap with the already proved common residue modulo four."
      formalStatement := "d_G(v_i)=d_G(v_j)\\quad\\lor\\quad d_G(v_i)\\ne d_G(v_j)\\ \\wedge\\ d_G(v_i)\\equiv d_G(v_j)\\pmod 4"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-prefix-degree-refinement", title := "Two-occurrence exact degree refinement", nodeIds := [179] }
      ]
      declarationGroups := [{
        groupId := "p13-long-prefix-degree-total"
        title := "Exact collision provenance and two local degree rows"
        role := .semanticTheorem
        explanation := "The source re-exposes the exact node-[164] result, promoted CT10 response-context field, and literal vertices. The classifier compares their full degrees and preserves distinctness, packing-bit equality, and residue equality in both branches."
        declarations := [
          `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_node164,
          `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_ct10_promotion_responseContexts,
          `Erdos64EG.Internal.p13SameWindowLongPrefixDegree_firstVertex_exact,
          `Erdos64EG.Internal.p13SameWindowLongPrefixDegree_secondVertex_exact,
          `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.run,
          `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.source_occurrences_distinct,
          `StructuralExhaustion.Graph.LongPrefixDegreeRefinement.visibleChecks_le,
          `Erdos64EG.Internal.P13SameWindowLongPrefixDegreeSource.exact_ct10_run,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_distinct,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixDegreeRefinement_ambient_preserved
        ]
      }]
      scopeNotes := "Node [179] proves only exact degree refinement. It does not construct D4--D7 responses, response equivalence, CT8 removal, or a smaller object; those remain white node [183]."
      workBound := "Exactly 2|V|+1 visible local degree checks, at most 2(|V|+1). No response, context, state, graph, or universe enumeration."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-response-consumer"
      stageId? := some "proof-slice.p13-long-prefix-local-clause-alignment"
      title := "First-nine local-clause alignment"
      plainExplanation := "Node [183] retains the exact node-[179] degree branch and CT10 obligation, then compares adjacency of its two literal vertices on exactly the same nine prefix coordinates."
      formalStatement := "(\\exists\\text{ first mismatch below }9)\\ \\lor\\ (\\forall i<9,\\ A(v,i)=A(w,i))"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-local-clause-alignment", title := "First-nine local-clause alignment", nodeIds := [183] }]
      declarationGroups := [{
        groupId := "p13-long-prefix-local-alignment-total"
        title := "Exact node-[179] source and nine local adjacency clauses"
        role := .semanticTheorem
        explanation := "The first-hit classifier returns a sound first mismatch with a clean prefix or alignment limited to the nine supplied coordinates. Both degree constructors are retained without semantic interpretation."
        declarations := [
          `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.run,
          `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment.visibleChecks_constant,
          `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.exact_node179,
          `Erdos64EG.Internal.P13SameWindowLongPrefixLocalClauseSource.retained_ct10_responseContexts,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixLocalClauseAlignment_ambient_preserved
        ]
      }]
      scopeNotes := "Node [183] proves alignment on nine clauses only, not D4--D7 response equivalence or CT8 removal; those remain white node [186]."
      workBound := "Exactly 18 local adjacency evaluations. No ambient response, context, state, graph, or universe enumeration."
    },
    {
      stepId := "erdos.p13-long-prefix-full-response-consumer"
      stageId? := some "proof-slice.p13-long-prefix-extended-clause-alignment"
      title := "First-eighteen local-clause alignment"
      plainExplanation := "Node [186] passes through an inherited mismatch or scans only literal positions 9--17 after first-nine alignment, yielding a second mismatch or first-eighteen alignment."
      formalStatement := "\\text{mismatch below 18}\\ \\lor\\ \\forall i<18,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-extended-clause-alignment", title := "First-eighteen local-clause alignment", nodeIds := [186] }]
      declarationGroups := [{
        groupId := "p13-extended-local-alignment"
        title := "Exact second-block scan"
        role := .semanticTheorem
        explanation := "The runner retains nested node-[179]/CT10 provenance and scans exactly the second nine literal coordinates."
        declarations := [
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.run,
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.exact_node183,
        `Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixExtendedClauseAlignment_ambient_preserved
      ] }]
      scopeNotes := "Node [186] proves first-eighteen adjacency alignment only, not full response equivalence or CT8; those remain white node [189]."
      workBound := "At most 18 new adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-response-semantics"
      stageId? := some "proof-slice.p13-long-prefix-third-block-clause-alignment"
      title := "First-twenty-seven local-clause alignment"
      plainExplanation := "Node [189] passes through either inherited mismatch unchanged or scans only literal positions 18--26 after first-eighteen alignment."
      formalStatement := "\\text{mismatch below 27}\\ \\lor\\ \\forall i<27,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-third-block-clause-alignment", title := "First-twenty-seven local-clause alignment", nodeIds := [189] }]
      declarationGroups := [{
        groupId := "p13-third-block-local-alignment"
        title := "Exact third-block scan"
        role := .semanticTheorem
        explanation := "The runner preserves node-[186], degree, and CT10 provenance; earlier mismatches pass through and only the third nine-coordinate block is newly scanned."
        declarations := [
          `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.run,
          `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.source_extended_exact,
          `StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment.visibleChecks_polynomial,
          `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.exact_node186,
          `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.retained_degree_result,
          `Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.retained_ct10_responseContexts,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixThirdBlockClauseAlignment_ambient_preserved
        ]
      }]
      scopeNotes := "Node [189] proves only first-twenty-seven adjacency alignment, not response equivalence or CT8; those remain white node [192]."
      workBound := "At most 18 new local adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-full-semantics"
      stageId? := some "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      title := "First-thirty-six local-clause alignment"
      plainExplanation := "Node [192] passes through all earlier mismatch leaves and otherwise scans only literal positions 27--35."
      formalStatement := "\\text{mismatch below 36}\\ \\lor\\ \\forall i<36,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-fourth-block-clause-alignment", title := "First-thirty-six local-clause alignment", nodeIds := [192] }]
      declarationGroups := [{
        groupId := "p13-fourth-block-local-alignment"
        title := "Exact fourth-block scan"
        role := .semanticTheorem
        explanation := "The exact node-[189] result, degree residual, and CT10 obligation are retained; only the fourth nine-coordinate block is newly scanned."
        declarations := [
          `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.run,
          `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.source_third_exact,
          `StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment.visibleChecks_polynomial,
          `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.exact_node189,
          `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.retained_degree_result,
          `Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.retained_ct10_responseContexts,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixFourthBlockClauseAlignment_ambient_preserved
        ]
      }]
      scopeNotes := "Node [192] proves only first-thirty-six adjacency alignment; node [195] records the terminal response/CT8 residual."
      workBound := "At most 18 new local adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-response-producer"
      stageId? := some "proof-slice.p13-long-prefix-compatible-response-frontier"
      title := "Long-prefix compatible-response frontier"
      plainExplanation := "Node [195] retains all five node-[192] leaves and their degree and CT10 provenance, then exposes only the graph-owned response and CT8 requirements still missing on each leaf."
      formalStatement := "\\text{node-[192] leaf}\\Longrightarrow\\text{same leaf plus explicit response residual}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-compatible-response-frontier", title := "Compatible-response frontier", nodeIds := [195] }]
      declarationGroups := [{
        groupId := "p13-long-prefix-compatible-response-frontier"
        title := "Exact five-leaf residual frontier"
        role := .semanticTheorem
        explanation := "The graph layer passes every mismatch or aligned leaf through unchanged and attaches at most three explicit graph-owned requirements. The application retains node [192], degree provenance, and the CT10 response-context tag."
        declarations := [
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_predecessor,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.requiredInputs_le_three,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.visibleChecks_constant,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_degree_result,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_ct10_responseContexts,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_requiredInputs,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_ambient_preserved
        ]
      }]
      scopeNotes := "Finite adjacency alignment is not response equivalence; this terminal interface proves no distinguishing context, removal, or CT8 conclusion."
      workBound := "One constructor inspection and at most three fixed requirement tags."
    },
    {
      stepId := "erdos.p13-same-window-dyadic-terminal"
      stageId? := some "proof-slice.p13-same-window-dyadic-terminal"
      title := "Computed dyadic frontier constructor closes"
      plainExplanation := "When the computed node-[159] result is its dyadic constructor, the adapter uses that constructor's canonical stub position and restored root cycle—without accepting another witness—to build the exact cold dyadic hit. The existing one-check CT1 G1 runner reaches C1, contradicting the inherited target-avoidance field."
      formalStatement := "\\mathcal R(P)=\\operatorname{dyadic}(s,C)\\Longrightarrow \\operatorname{Target}(G)\\Longrightarrow\\bot"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-same-window-dyadic-terminal", title := "Dyadic constructor closes", nodeIds := [155] }
      ]
      declarationGroups := [
        {
          groupId := "p13-computed-dyadic-provenance"
          title := "Computed constructor and exact cold hit"
          role := .compositionProvenance
          explanation := "The branch object records equality with the computed node-[159] dyadic constructor. Its cold hit has exactly the same window, stub offset, first-hit payload, and restored root-cycle walk."
          declarations := [
            `Erdos64EG.Internal.runP13SameWindowStructuralFrontier,
            `Erdos64EG.Internal.P13ComputedDyadicBranch,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit_offset,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.stub_window,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.coldDyadicHit_cycle_eq_rootCycle
          ]
        },
        {
          groupId := "p13-computed-dyadic-ct1-interface"
          title := "Existing proof-carrying CT1 target interface"
          role := .frameworkInterface
          explanation := "The framework converts the supplied target cycle to its rooted return and validates it through the established CT1 encoding. The existing G1 endpoint then compares the certified target directly with the same context's avoiding field."
          declarations := [
            `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.runCycleAsRootedReturnCT1,
            `Erdos64EG.P13ColdGermTerminalRoutes.g1Run,
            `Erdos64EG.P13ColdGermTerminalRoutes.g1_impossible
          ]
        },
        {
          groupId := "p13-computed-dyadic-execution"
          title := "One-check C1 execution and closure"
          role := .executionAudit
          explanation := "The thin node-[159] consumer exposes the exact C1 terminal, typed trace, one-check count, and final contradiction."
          declarations := [
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1Run,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_terminal,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_trace,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_checks,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.impossible
          ]
        }
      ]
      scopeNotes := "Node [155] is green only as the consumer of node [159]'s computed dyadic constructor. This does not construct a bounded germ, close the surplus or quiet constructors, or validate the separate aggregate G1 producer claimed after nodes [153]–[154]."
      workBound := "One supplied-certificate CT1 check after the already accounted node-[159] scan; no cycle, walk, graph, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-positive-deficiency"
      stageId? := some "proof-slice.p13-positive-deficiency"
      title := "Positive deficiency of the exact P13 remainder"
      plainExplanation := "The graph charge layer computes the induced degree of every vertex in the exact CT12 remainder and sums the natural deficit 3-d_R(v), which is exactly max(0,3-d_R(v)). The no-internal-three-core predecessor is retained unchanged."
      formalStatement := "\\operatorname{def}^{+}(R)=\\sum_{v\\in R}\\max\\{0,3-d_R(v)\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:deficiency-surplus", title := "Positive deficiency and surplus", nodeIds := [28] }
      ]
      declarationGroups := [{
        groupId := "p13-remainder-positive-deficiency"
        title := "Framework-owned induced-support charge definition"
        role := .mathematicalDefinition
        explanation := "The reusable graph profile owns induced degree and positive deficiency. The application instantiates its core with the exact node-[27] remainder finset and proves the displayed sum definitionally."
        declarations := [
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.internalDegree,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.positiveDeficiency,
          `Erdos64EG.Internal.p13RemainderDeficiencyProfile,
          `Erdos64EG.Internal.p13Remainder_internalDegree_eq,
          `Erdos64EG.Internal.p13Remainder_positiveDeficiency_eq,
          `Erdos64EG.Internal.exists_verifiedP13PackingPrefix,
          `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix
        ]
      }]
      scopeNotes := "Node [28] is complete and consumes only the green node-[27] remainder. Its exact output is consumed unchanged by the green node-[29] incidence ledger."
      workBound := "One induced-neighbour scan per remainder vertex, bounded quadratically in the declared graph order; no subgraph or support family is enumerated."
    },
    {
      stepId := "erdos.remainder-curvature-rank"
      stageId? := some "proof-slice.p13-curvature-rank"
      title := "Exact remainder incidence, wedge, and curvature rank"
      plainExplanation := "The framework consumes the exact node-[28] remainder. Every deficient unit is charged to a literal edge leaving that remainder, every such edge occurs in the selected-window token schedule, and the exact identity for that schedule gives 15p₁₃+σ_W. The raw coordinate type is one center plus a canonical unordered pair of its internal remainder neighbours, so its cardinality is exactly W₂(R). CT15 scans those coordinates and certified-reduction admissibility makes the full-rank terminal unconditional."
      formalStatement := "\\operatorname{def}^{+}(R)\\le15p_{13}+\\sigma_W,\\quad \\operatorname{def}^{+}(R)-\\sigma_R\\le15p_{13}+\\sigma_W-\\sigma_R,\\quad W_2(R)\\ge3|R|-2\\operatorname{def}^{+}(R),\\quad r_\\Omega(R)=W_2(R)"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "lem:stub-positive", title := "External-incidence supply", nodeIds := [29] },
        { label := "lem:surplus-aware-window-stub", title := "Exact surplus-aware stub bound", nodeIds := [29] },
        { label := "lem:wedge-lower", title := "Wedge lower bound", nodeIds := [30] },
        { label := "def:curvature-target-rank", title := "Curvature target-rank", nodeIds := [31] },
        { label := "lem:target-rank-circuit", title := "Rank decision", nodeIds := [32, 33, 34, 35] },
        { label := "lem:full-rank", title := "Forcing of full curvature rank", nodeIds := [34] }
      ]
      declarationGroups := [
        {
          groupId := "remainder-deficiency-wedge-kernel"
          title := "Framework-owned exact graph accounting"
          role := .semanticTheorem
          explanation := "The reusable graph profile owns internal degree, boundary incidence, positive deficiency, raw wedge count, the deficiency injection, and the exact finite wedge floor."
          declarations := [
            `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.positiveDeficiency_le_boundaryIncidences,
            `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeFloor,
            `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeCount_le_cube,
            `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount,
            `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_tokenCount,
            `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus,
            `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le,
            `StructuralExhaustion.Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus
          ]
        },
        {
          groupId := "remainder-curvature-ct15"
          title := "Literal wedge coordinates and CT15 execution"
          role := .compositionProvenance
          explanation := "The Erdős layer supplies only the exact remainder and the three-vertex support of each actual wedge. The generic response profile and admissible-quotient CT15 runner own the decision, trace, validity, and linear coordinate scan."
          declarations := [
            `Erdos64EG.Internal.p13CurvatureCoordinates,
            `Erdos64EG.Internal.p13CurvatureCoordinates_card_eq_wedgeCount,
            `Erdos64EG.Internal.p13CurvatureCoordinates_card_le_cube,
            `Erdos64EG.Internal.p13CurvatureResponseProfile,
            `StructuralExhaustion.Graph.FiniteSupportResponse.Profile.run,
            `Erdos64EG.Internal.runP13CurvatureCT15_terminal,
            `Erdos64EG.Internal.runP13CurvatureCT15_trace,
            `Erdos64EG.Internal.no_p13Curvature_rankDrop,
            `Erdos64EG.Internal.exists_verifiedP13PositiveDeficiencyPrefix,
            `Erdos64EG.Internal.exists_verifiedP13CurvaturePrefix
          ]
        }
      ]
      scopeNotes := "Nodes [29]--[35] are complete on the unchanged green node-[28] remainder. The exact finite inequalities are stronger than their normalized o(n) manuscript corollaries. The rank-drop constructor is proved empty for the selected minimal graph, so the existing conditional nodes [36]--[39] have a valid but unreachable input rather than an assumed certificate."
      workBound := "At most quadratic neighbour-incidence work on the supplied graph plus one linear CT15 scan of the literal wedge schedule; the graph kernel proves that schedule has at most n³ coordinates. No connected-support, path, quotient, context, subgraph, or graph family is enumerated."
    },
    {
      stepId := "erdos.proper-delocalization-closure"
      stageId? := some "proof-slice.proper-delocalization"
      title := "Proper enlarged-support smearing closure"
      plainExplanation := "An enlarged determination certificate records a connected proper support Z, an embedding of the original atom, and strict support growth. The next tag decides whether the enlarged support is proper or whole-graph. In the proper case the framework compares the exact response against all outside contexts: a mismatch is the target-defect residual, while universal agreement constructs the existing literal CT3 compression and contradicts minimality."
      formalStatement := "C\\subsetneq Z\\subsetneq G\\Longrightarrow\\text{target defect or impossible proper-support compression}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:curvature-dependence-routing", title := "Enlarged connected support route", nodeIds := [40] },
        { label := "lem:proper-smearing", title := "Proper delocalization supports are forbidden", nodeIds := [41, 42] }
      ]
      declarationGroups := [{
        groupId := "proper-delocalization-ct3-route"
        title := "Framework-owned proper/whole split and CT3 closure"
        role := .semanticTheorem
        explanation := "The graph layer owns the extension certificate, proper-versus-whole tag, universal context audit, exact CT3 compression execution, and total route. The Erdős layer is a thin instantiation on the selected packed minimal context."
        declarations := [
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.RankDropRouting.verifiedStage,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.targetDefective,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.compression_terminal,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.ProperExtension.compression_trace,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.Location,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.route,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.routeAfterRankDrop,
          `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperDelocalization.verifiedStage,
          `Erdos64EG.Internal.routeProperDelocalization,
          `Erdos64EG.Internal.routeRankDropThroughProperDelocalization,
          `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix
        ]
      }]
      scopeNotes := "Nodes [40]--[42] are complete and consume only the green rank-drop routing interface at nodes [36]--[39]. The whole-graph constructor preserves the exact closed-proposal payload consumed by the next verified block."
      workBound := "One supplied context-universality proposition and, on its universal side, one constant-work certified CT3 reduction. No contexts, supports, quotients, subgraphs, or graphs are generated."
    },
    {
      stepId := "erdos.global-rank-drop-closure"
      stageId? := some "proof-slice.global-rank-drop-closure"
      title := "Whole-support rank-drop closure"
      plainExplanation := "The whole-graph constructor carries one concrete quotient already admitted by the finite exact-profile contract, together with the two distinct coordinates identified by the alleged rank drop. The framework derives injectivity from the quotient's certified-reduction field and minimality, so the identification is impossible. Separately, the graph layer computes the one--three repair identity from one literal connected finite component."
      formalStatement := "s=p-2+2\\beta_Z-\\sigma_Z,\\qquad Z=G\\Longrightarrow\\text{the admitted quotient is injective and the rank drop closes}"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "lem:no-silent-global-smearing", title := "Whole-graph delocalization barrier", nodeIds := [43, 45] },
        { label := "lem:smearing-support-repair", title := "One--three repair identity", nodeIds := [44] },
        { label := "lem:full-rank", title := "Rank-drop closure and full-rank join", nodeIds := [46, 47] }
      ]
      declarationGroups := [
        {
          groupId := "closed-rank-drop-route"
          title := "Framework-owned admitted-quotient barrier"
          role := .semanticTheorem
          explanation := "The CT15 admission contract already contains response preservation and a certified reduction for every non-injective code. The graph layer derives exact label injectivity and closes a literal distinct-coordinate identification. The Erdős layer supplies the wedge response system and composes the inherited admitted payload."
          declarations := [
            `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.injective,
            `StructuralExhaustion.Graph.ClosedRankDrop.exactBarrier,
            `StructuralExhaustion.Graph.ClosedRankDrop.no_silent_identification,
            `StructuralExhaustion.Graph.ClosedRankDrop.rankDrop_impossible,
            `Erdos64EG.Internal.P13WholeDelocalization,
            `Erdos64EG.Internal.routeRankDropThroughGlobalClosure,
            `Erdos64EG.Internal.p13ClosedRankDrop_exactBarrier,
            `Erdos64EG.Internal.no_p13Closed_silentIdentification,
            `Erdos64EG.Internal.p13WholeDelocalization_impossible,
            `Erdos64EG.Internal.exists_verifiedP13ProperDelocalizationPrefix
          ]
        },
        {
          groupId := "one-three-repair-arithmetic"
          title := "Framework-owned handshake and cycle-rank identity"
          role := .semanticTheorem
          explanation := "The core theorem derives the exact repair identity in integer arithmetic from the handshake and connected cycle-rank equations, avoiding truncated subtraction."
          declarations := [
            `StructuralExhaustion.Core.OneThreeRepair.identity,
            `StructuralExhaustion.Graph.OneThreeRepair.Component.identity,
            `Erdos64EG.Internal.oneThreeRepair_identity,
            `Erdos64EG.Internal.oneThreeRepair_component_identity,
            `Erdos64EG.Internal.exists_verifiedP13GlobalRankClosurePrefix
          ]
        }
      ]
      scopeNotes := "Nodes [43]--[47] implement the complete local admitted-quotient closure. Node [46] is closed by the contradiction between injectivity and the retained distinct-coordinate identification; node [47] is the unconditional full-rank join. Node [48] remains white: quotient injectivity is not treated as Boolean-product realization."
      workBound := "One certified-reduction check for the supplied admitted quotient; no contexts, quotient family, support family, graph family, or Boolean cube is enumerated."
    },
    {
      stepId := "erdos.closure-robust-part-iv"
      title := "Closure-robust window-only Part IV"
      plainExplanation := "The production Part-IV spine does not enumerate ambient vertices or require a Boolean-product realization. It exposes the exact same-context node-24 theorem still owed by the genuine fixed cold-skeleton/F2--F5 proof: a packing ceiling, the cross-multiplied finite form of the printed window-density cap, and the finite strict-quarter window budget. Once that theorem is supplied, the verified node-47 predecessor composes directly through the node-55 budget to the literal node-56 net-deficiency bound."
      formalStatement := "\\mathsf{WindowDensity}_{24}(G)\\Longrightarrow 4\\bigl(D^+(R)-\\sigma_R\\bigr)<|R|"
      status := .next
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "prop:p13-density", title := "Window-only P13 density", nodeIds := [24] },
        { label := "rem:closure-robust", title := "Closure without forced curvature cost", nodeIds := [47, 54, 55, 56] },
        { label := "lem:netcharge-superadd", title := "Net-charge quarter handoff", nodeIds := [55, 56] }
      ]
      declarationGroups := []
      scopeNotes := "This is a typed partial frontier, not a green Part-IV closure. The node-47-to-node-56 composition is verified, but no production declaration currently inhabits the strengthened P13WindowDensityStructuralTheorem; node [24] and therefore nodes [48]--[56] remain unclosed. The exact node-[21]-to-Part-XI four-way partition is available, but its non-dyadic outputs lack the aggregate bounded-multiplicity and D4--D7 consumers needed to prove this cap. P13PartIVFiniteRouting is deliberately absent from the production import graph and serves only as a negative audit of the invalid ambient-state enumeration route."
      workBound := "After the structural node-24 theorem, the composition is constant-size arithmetic. The missing proof must use the genuine fixed cold-skeleton/F2--F5 local argument; it may not enumerate vertices, states, supports, contexts, subgraphs, or graph families."
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
        "The CT6 surplus cardinality and the per-slot return/suppression or triangular activation are implemented. The exact activated output is retained by node [129]'s baseline-demand stage; the complete pair-response split at nodes [130]--[132] remains downstream."
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
        { label := "lem:heavy-neighbourhood-normal-form", title := "High-neighbourhood normal form", nodeIds := [67, 69] }
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
        { label := "def:surplus-ports", title := "Surplus ports and excess selectors" },
        { label := "def:heavy-center-triangular-port", title := "High centers and port types", nodeIds := [69, 78] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69, 78] }
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
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69] }
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
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69, 130] },
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
        { label := "def:surplus-ports", title := "Surplus ports and shoulder pairs" },
        { label := "def:triangular-fan-core", title := "Triangular fan shoulders", nodeIds := [79] },
        { label := "rem:finite-selected-port-audit", title := "Finite selected-port audit", nodeIds := [69, 79] }
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
      stepId := "erdos.degree-four-type-b-ledger"
      stageId? := some "proof-slice.degree-four-type-b-ledger"
      title := "Exact degree-four Type B fan ledger"
      plainExplanation :=
        "The negative side of the higher-centre test proves that every actual high centre has degree exactly four. CT14 then scans its four incident ports, computes the exact cubic-closed count and quarter-deficit, and an independent finite marking scan routes the same centre to its assigned fan certificate or to the literal no-certificate residual."
      formalStatement :=
        "(\\neg\\exists h,\\ d(h)>4)\\Longrightarrow\\forall h,\\ d(h)=4\\land 0\\le c(h)\\le4\\land D_B(h)=c(h)-7/4\\land(S_h\\text{ is assigned}\\ \\lor\\ S_h=\\varnothing)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "cor:degree-four-local-activation", title := "Degree-four local activation", nodeIds := [68, 78] },
        { label := "def:typeB-window-incidence-profile", title := "Degree-four fan profile", nodeIds := [79] },
        { label := "def:marked-typeB-fan", title := "Assigned certificate marking", nodeIds := [80] }
      ]
      declarationGroups := [{
        groupId := "degree-four-type-b-ct14"
        title := "Framework-owned degree-four fan and certificate ledgers"
        role := .semanticTheorem
        explanation := "The graph layer owns the exact four-port CT14 scan, closed-count arithmetic, and finite certificate marking. The Erdős layer derives degree four from the actual high-centre schedule and composes both ledgers without a global graph enumeration."
        declarations := [
          `StructuralExhaustion.Graph.DegreeFourFanLedger.members_card_eq_degree,
          `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedStage,
          `StructuralExhaustion.Graph.FiniteCertificateMarking.Profile.marked_or_residual,
          `Erdos64EG.Internal.TypeBSupportScope.degree_eq_four_of_noHigher,
          `Erdos64EG.Internal.TypeBSupportScope.higher_or_degreeFour_certificateFlow,
          `Erdos64EG.Internal.exists_verifiedDegreeFourTypeBLedgerPrefix
        ]
      }]
      scopeNotes := "This completes nodes [78]--[80] locally. The node-[80] yes branch retains the exact assigned marked fan; its no branch retains the literal equality assignedMarkedFan(h)=none for the fan-mass route. Neither outcome assumes the later B1/B2 decision."
      workBound := "Each centre scans exactly four incident ports and one optional certificate; over the actual high-centre schedule the proved bound is 23(|V|+1)^2."
    },
    {
      stepId := "erdos.degree-four-b2-routing"
      stageId? := some "proof-slice.degree-four-b2-routing"
      title := "Exact local-entry and B2 exhaustion"
      plainExplanation := "Every local certificate-closed or positive-B1 entry must use the exact Option certificate assigned at node [80]. The finite resolution scan and CT12 then return an unresolved actual center, a full disjoint choice with nonnegative charge or a literal remaining negative core, or a proof-carrying minimal overlap obstruction."
      formalStatement := "\\operatorname{Unresolved}(h)\\ \\lor\\ \\operatorname{No}(X)\\ge0\\ \\lor\\ \\operatorname{Remaining}(X)<0\\ \\lor\\ \\operatorname{MinimalOverlap}(X)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-hybrid-B1", title := "Local B1 incidence budget", nodeIds := [81] },
        { label := "lem:typeB-bridge-to-overlap", title := "B2 failure gives minimal overlap", nodeIds := [81, 83] },
        { label := "lem:typeB-exclusion", title := "Nonnegative full-choice branch outside the remaining residual", nodeIds := [82] }
      ]
      declarationGroups := [{
        groupId := "degree-four-b2-total-route"
        title := "Framework finite resolution and CT12 B2 route"
        role := .semanticTheorem
        explanation := "The provenance-refined local-entry subtype prevents a later certificate substitution. Generic finite resolution and the existing CT12 completion own the exhaustive split; the graph-charge theorem owns the full-choice nonnegative/remaining-negative alternative."
        declarations := [
          `StructuralExhaustion.Core.FiniteResolution.Profile.fullResolution_or_unresolved,
          `StructuralExhaustion.CT12.RefinedLedgerCompletion.Profile.verifiedStage,
          `Erdos64EG.Internal.TypeBSupportScope.unresolved_of_certificate_none,
          `Erdos64EG.Internal.TypeBSupportScope.certificateResidual_is_unresolved,
          `Erdos64EG.Internal.TypeBSupportScope.fullResolution_entry_provenance,
          `Erdos64EG.Internal.TypeBSupportScope.degreeFourB2Route,
          `Erdos64EG.Internal.TypeBSupportScope.fullChoice_nonnegative_or_remainingNegative,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_disjoint_choice,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.proper_subschedule_has_choice,
          `Erdos64EG.Internal.TypeBAssignedSupport.MinimalOverlap.no_separated_carrier_partition,
          `Erdos64EG.Internal.exists_verifiedDegreeFourTypeBLedgerPrefix,
          `Erdos64EG.Internal.exists_verifiedDegreeFourB2RoutingPrefix
        ]
      }]
      scopeNotes := "Nodes [81]--[83] are complete. Missing or incoherent local entries are explicit fan-mass residuals; a full choice is split by the literal graph charge; failure of the choice is the exact minimal CT12 overlap. No branch is discarded or converted into an assumption."
      workBound := "The local-entry scan is linear in actual high centers and CT12 peels each declared center once. Candidate products, demand subsets, graph families, and support families are not evaluated."
    },
    {
      stepId := "erdos.type-b-residual-center-ledger"
      stageId? := some "proof-slice.type-b-residual-center-ledger"
      title := "Ordinary Type B residual centers use assigned surplus"
      plainExplanation := "Certificate failures, unresolved local entries, and every center selected by a minimal B2 obstruction remain actual members of the same high-center schedule. The graph charge profile proves their finite cardinality is at most the assigned surplus sum."
      formalStatement := "|H_{\\rm residual}(X)|\\le\\sum_{h\\in H_X}(d_G(h)-3)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:typeB-residual-mass", title := "Type B residual fan mass", nodeIds := [75] },
        { label := "lem:typeB-bridge-deficit-bound", title := "Assigned residual-center budget", nodeIds := [75] }
      ]
      declarationGroups := [{
        groupId := "type-b-residual-center-charge"
        title := "Graph-derived assigned-surplus payer ledger"
        role := .semanticTheorem
        explanation := "The reusable high-center charge theorem pays every finite subtype of actual high centers. The Erdős layer identifies the certificate, unresolved, and minimal-overlap center lists with such subtypes and retains their exact provenance."
        declarations := [
          `StructuralExhaustion.Graph.HighCenterDeletionCharge.Profile.centers_card_le_assignedSurplus,
          `Erdos64EG.Internal.TypeBSupportScope.residualCenters_card_le_assignedSurplus,
          `Erdos64EG.Internal.TypeBSupportScope.certificateResidual_charged,
          `Erdos64EG.Internal.TypeBSupportScope.unresolved_charged,
          `Erdos64EG.Internal.TypeBSupportScope.minimalOverlapCenters_charged,
          `Erdos64EG.Internal.TypeBSupportScope.minimalOverlap_has_assignedSurplus,
          `Erdos64EG.Internal.exists_verifiedDegreeFourB2RoutingPrefix,
          `Erdos64EG.Internal.exists_verifiedTypeBResidualCenterLedgerPrefix
        ]
      }]
      scopeNotes := "Node [75] is complete for the ordinary assigned-support role: every local negative outcome has an actual high-center payer and no center is duplicated inside the finite residual set. The later node [84] two-role grouped-envelope mass coefficient is not claimed here."
      workBound := "Linear finite-set and subschedule cardinality proofs over actual high centers. No support family, envelope family, graph family, or global matching is enumerated."
    },
    {
      stepId := "erdos.type-b-local-fan-mass"
      stageId? := some "proof-slice.type-b-local-fan-mass"
      title := "Local selected-center Type B fan mass"
      plainExplanation := "CT14 consumes one exact predecessor Type B scope. For every literal selected high-center set, unit lower mass is paid by the same centers' graph-derived degree surplus; the nonnegative, route-8, and minimal-overlap branches are retained unchanged."
      formalStatement := "|S|\\le\\sum_{h\\in H_X}(d_G(h)-3)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-local-selected-fan-mass", title := "Local selected-center fan-mass bound", nodeIds := [84] }
      ]
      declarationGroups := [{
        groupId := "type-b-local-selected-mass-ct14"
        title := "Framework-owned selected-surplus CT14 scan"
        role := .semanticTheorem
        explanation := "The generic graph profile scans only the literal center schedule. The Erdős wrapper executes the exhaustive predecessor route and identifies the exact singleton or minimal-overlap selected set."
        declarations := [
          `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedStage,
          `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.selectedCount_le_totalSurplus,
          `Erdos64EG.Internal.TypeBSupportScope.localFanMass,
          `Erdos64EG.Internal.TypeBSupportScope.overlapCenters_card_eq_selected_length,
          `Erdos64EG.Internal.TypeBSupportScope.localFanMassRoute,
          `Erdos64EG.Internal.exists_verifiedTypeBLocalFanMassPrefix
        ]
      }]
      scopeNotes := "Node [84] consumes exactly green node [75] and nodes [81]--[83]. It proves only the local per-scope mass statement. The unsupported canonical ordinary/grouped family and coefficient 208 are isolated at white node [176]."
      workBound := "Exactly 4k+1 CT14 profile calls on k actual high centers; the list-membership comparison ledger is at most 5(k+1)^2. No support family, subset family, path family, graph family, or global matching is enumerated."
    },
    {
      stepId := "erdos.type-b-global-fan-mass"
      title := "Global grouped Type B fan-mass producer"
      plainExplanation := "The open consumer must construct the canonical ordinary/grouped support family, prove within-role incidence control and both coefficient-208 semantic bounds, and only then derive the factor-416 global estimate."
      formalStatement := "M_B\\le 416\\sum_{h}(d_G(h)-3)"
      status := .next
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:typeB-processed-boundary-bound", title := "Processed-envelope boundary bound", nodeIds := [176] },
        { label := "prop:typeB-bridge-sublinear", title := "Global grouped Type B fan-mass discharge", nodeIds := [176] }
      ]
      declarationGroups := []
      scopeNotes := "This node has no constructor from the local node-[84] prefix. It must supply an actual support-indexed producer; the coefficient and grouped-family realization are not assumptions."
      workBound := "Any implementation must scan only a produced finite support/incidence list. Ambient support families, vertex subsets, paths, graphs, and colorings may not be enumerated."
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
        { label := "def:triangular-fan-core", title := "Triangular fan core and shoulder completions" },
        { label := "lem:triangular-shoulder-completion", title := "Shoulder-completion bookkeeping" }
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
        { label := "lem:triangular-port-return", title := "Port returns enter through shoulders" }
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
        { label := "lem:triangular-first-landing", title := "First landing exhaustion for triangular shoulders" }
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
        { label := "lem:triangular-cross-shoulder", title := "Cross-shoulder multiplicity" }
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
          `Erdos64EG.Internal.routeSurplusScale_exhaustive,
          `Erdos64EG.Internal.exists_verifiedSparseSurplusPrefix,
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
          `Erdos64EG.Internal.exists_verifiedSparseEnvelopePrefix,
          `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure,
          `Erdos64EG.Internal.verifiedSparseEnvelopeFromPressure_sameLabelPrefix
        ]
      }]
      scopeNotes := "This verifies the complete node [126] block, including both displayed identities. Its output is retained unchanged by the activated surplus family and baseline-demand stages."
      workBound := "CT12 performs exactly n-1 peeling iterations on one proof-selected vertex list and has a linear polynomial check budget. The edge theorem uses well-founded recursion on strictly smaller explicit supports; no graph, subgraph, order, path, or context universe is enumerated."
    },
    {
      stepId := "erdos.baseline-spine-demand"
      stageId? := some "proof-slice.baseline-spine-demand"
      title := "Activated surplus family and baseline spine demand"
      plainExplanation := "Nodes [127]--[128] attach the CT2-derived root return and exact open-suppression or triangular response to every slot in the already verified CT6 surplus ledger. Node [129] then defines a baseline demand as an independently target-testable finite coordinate family with explicit deficit. The canonical empty family is an unconditional instance, and CT15 returns its exact full-rank ledger without assuming a later linear-deficit estimate."
      formalStatement := "b_0=\\lfloor\\log_2\\binom{\\binom n2}{\\lceil3n/2\\rceil}\\rfloor,\\qquad |\\mathcal I_{\\rm spine}|=0\\ge b_0-b_0"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:sparse-excess-port-extraction", title := "Excess-port extraction", nodeIds := [127] },
        { label := "lem:sparse-port-activation", title := "Sparse port activation", nodeIds := [128] },
        { label := "lem:surviving-active-family", title := "Surviving active family", nodeIds := [127, 128] },
        { label := "def:baseline-spine-demand", title := "Baseline spine demand", nodeIds := [129] }
      ]
      declarationGroups := [{
        groupId := "surplus-port-activation"
        title := "Exact per-slot activation on the retained CT6 ledger"
        role := .compositionProvenance
        explanation := "The reusable graph layer derives each response from CT2 bridgelessness and packed minimality, retains the exact local support, and proves that the activated schedule is the unchanged CT6 schedule. The Erdős layer supplies only the power-of-two length interpretation and the selected minimal context."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPortActivation.verifiedActivatedStageFromMinimality,
          `StructuralExhaustion.Graph.SurplusPortActivation.activatedSchedule_length_eq_residualTotal,
          `Erdos64EG.Internal.surplusPortActivationSetup,
          `Erdos64EG.Internal.activatedSurplusStage,
          `Erdos64EG.Internal.activeSurplusDemand,
          `Erdos64EG.Internal.activatedSurplusSchedule_length_eq_sigma,
          `Erdos64EG.Internal.openResponse_has_mersenne_length,
          `Erdos64EG.Internal.verifiedSurplusPortActivationPrefix,
          `Erdos64EG.Internal.exists_verifiedSurplusPortActivationPrefix
        ]
      }, {
        groupId := "baseline-spine-demand-ct15"
        title := "Exact finite baseline-demand profile and CT15 ledger"
        role := .semanticTheorem
        explanation := "The framework layer owns certified independent finite demands, their unit-charge full-rank ledgers, deterministic CT15 terminal and trace, soundness, totality, and linear work. The Erdős layer supplies only the exact cubic skeleton count and the canonical empty family with its explicit full deficit."
        declarations := [
          `StructuralExhaustion.CT15.BaselineDemand.Profile.verifiedStage,
          `StructuralExhaustion.CT15.run_terminal_eq_fullRankLedger_of_noDrop_of_total_le_capacity,
          `StructuralExhaustion.CT15.ledgerTotal_eq_card_of_charge_eq_one,
          `StructuralExhaustion.CT15.linearCheckBudget,
          `Erdos64EG.Internal.baselineSpineEdgeSlots,
          `Erdos64EG.Internal.baselineSpineEdgeCount,
          `Erdos64EG.Internal.baselineSpineStateCount,
          `Erdos64EG.Internal.baselineSpineBitBudget,
          `Erdos64EG.Internal.baselineSpineProfile,
          `Erdos64EG.Internal.baselineSpineProfile_coordinateCount,
          `Erdos64EG.Internal.baselineSpineProfile_exactDeficit,
          `Erdos64EG.Internal.baselineSpineProfile_lowerBound,
          `Erdos64EG.Internal.runBaselineSpineCT15_terminal,
          `Erdos64EG.Internal.runBaselineSpineCT15_trace,
          `Erdos64EG.Internal.runBaselineSpineCT15_verified,
          `Erdos64EG.Internal.runBaselineSpineCT15_total,
          `Erdos64EG.Internal.runBaselineSpineCT15_linearBudget,
          `Erdos64EG.Internal.exists_verifiedBaselineSpineDemandPrefix
        ]
      }]
      scopeNotes := "This verifies the exact node [129] definition and makes its deficit explicit. The manuscript does not derive an O(n) deficit from that definition; a nonempty coordinate construction with a separately verified linear deficit remains necessary before the entropy sandwich can imply a near-cubic bound."
      workBound := "CT15 makes two passes over the declared coordinate list plus one comparison. For the canonical empty family this is one constant check; no subsets, target states, graph families, or contexts are enumerated."
    },
    {
      stepId := "erdos.free-blocked-pair-response"
      stageId? := some "proof-slice.sparse-pair-responses"
      title := "Complete free/blocked pair-response split"
      plainExplanation := "Nodes [130] and [132] consume the exact activated surplus schedule. Each unordered pair is generated once and classified by a local scan of its two retained supports, returns, port roles, and suppression cycles. A free pair receives one shortest connector and one exact finite-support response coordinate. Raw profile or target mismatches are rejected by the quotient audit; every admitted non-injective quotient carries a certified smaller counterexample and is impossible by minimality. CT15 returns the audited quotient-rank ledger for exactly the free coordinates; the following CT9 route consumes both sides of this exact partition."
      formalStatement := "\\binom{\\mathcal A_0}{2}=\\Pi_{\\rm free}\\sqcup\\Pi_{\\rm blk}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:surplus-blockers", title := "Sparse surplus blockers", nodeIds := [130, 132] },
        { label := "def:sparse-canonical-connector", title := "Canonical sparse connector", nodeIds := [130] },
        { label := "def:sparse-pair-response", title := "Sparse pair-response coordinates", nodeIds := [130] },
        { label := "lem:sparse-pair-dependence-exit", title := "Pair quotient audit", nodeIds := [130, 132] }
      ]
      declarationGroups := [{
        groupId := "sparse-pair-response-ct15"
        title := "Framework-owned local blocker, connector, and CT15 contracts"
        role := .semanticTheorem
        explanation := "The core layer proves the exact finite-family partition. The graph layer derives preconnectedness from packed minimality, retains one shortest connector per free pair, builds literal finite-support response coordinates, and executes CT15. The Erdős layer only composes this stage with the exact activated output retained by the preceding prefix."
        declarations := [
          `StructuralExhaustion.Core.FiniteBlockerLedger.FamilyProfile.blocked_card_add_free_card,
          `StructuralExhaustion.Core.FiniteBlockerLedger.FamilyProfile.firstBlocker_sound,
          `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.preconnected_of_noProperCore,
          `StructuralExhaustion.Graph.FiniteConnector.exists_certificate,
          `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.no_boundary_mismatch,
          `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.no_target_mismatch,
          `StructuralExhaustion.CT15.AdmissibleQuotient.Admissible.injective,
          `StructuralExhaustion.CT15.AdmissibleQuotient.Profile.verifiedFor,
          `StructuralExhaustion.Graph.SurplusPairResponse.verifiedStage,
          `StructuralExhaustion.Graph.SurplusPairResponse.canonicalBlocker_sound,
          `Erdos64EG.Internal.exists_verifiedBaselineSpineDemandPrefix,
          `Erdos64EG.Internal.sparsePairResponseStage,
          `Erdos64EG.Internal.sparsePair_exact_partition,
          `Erdos64EG.Internal.sparsePairCT15_verified,
          `Erdos64EG.Internal.sparsePair_schedule_quartic,
          `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix
        ]
      }]
      scopeNotes := "The verified output is the exact admitted structural split: blocker types (a)--(c) and retained type (f) are locally scanned, while types (d) and (e) are complete raw-proposal audit records and are impossible on the admitted branch. Node [131] consumes the free subtype and node [134] consumes the blocked subtype."
      workBound := "The slot schedule is at most quadratic and each unordered pair occurs once, so the pair schedule is at most n^4. Every pair scan touches only its two declared local supports, return paths, fixed port-role list, and retained cycles. A connector is proof-selected by finite endpoint minimization and verified from one retained shortest path; neither paths, connected subgraphs, quotient proposals, contexts, nor graphs are enumerated."
    },
    {
      stepId := "erdos.total-pair-token-route"
      stageId? := some "proof-slice.total-pair-token-route"
      title := "Exact free-anchor and blocker routing"
      plainExplanation := "Node [131] assigns every blocker-free pair to its canonical first selected surplus port with the distinct freeAnchor role. That port is already a primitive carrier token, and every member of its CT9 fibre is proved blocker-free, has that exact first port, and retains the shortest connector selected at node [130]. Blocked pairs retain their canonical first blocker and all earlier failed candidates for node [134]."
      formalStatement := "\\pi\\in\\Pi_{p,\\mathsf{freeAnchor}}\\Longrightarrow \\pi\\in\\Pi_{\\rm free},\\quad \\operatorname{first}(\\pi)=p"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:total-surplus-pair-token-route", title := "Five-role pre-retokenization dispatch and free-anchor route", nodeIds := [131] },
        { label := "lem:total-pair-token-route-no-overcount", title := "Free-anchor fibre clause", nodeIds := [131] }
      ]
      declarationGroups := [{
        groupId := "total-pair-token-route-ct9"
        title := "Framework-owned token--role ledger and graph route"
        role := .semanticTheorem
        explanation := "CT9 owns the finite product partition and bounded-fibre aggregation. The graph layer derives both role constructors directly from the blocker decision and exposes a typed primitive-audit input with retained connector data. The Erdős layer only composes this route with the exact prior prefix."
        declarations := [
          `StructuralExhaustion.CT9.TokenRoleLedger.noOvercounting,
          `StructuralExhaustion.CT9.TokenRoleLedger.bounded_total,
          `StructuralExhaustion.CT9.TokenRoleLedger.verifiedStage,
          `StructuralExhaustion.Graph.SurplusTokenRole.pairRouteRole_card,
          `StructuralExhaustion.Graph.SurplusTokenRole.totalRole_card,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.noOvercounting,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.free_role,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.blocked_role,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.freeAnchorFibre_member_is_free,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.freeAnchorFibre_member_first,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.blocked_retains_canonical_blocker,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_verified,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_traceValid,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.run_total,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.checks_le_five_mul_sixthPower,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.checks_le_five_mul_cube_of_token_card_le,
          `StructuralExhaustion.Graph.SurplusPairTokenRouting.verifiedStage,
          `Erdos64EG.Internal.exists_verifiedSparsePairResponsePrefix,
          `Erdos64EG.Internal.allPairTokenRoutingInput,
          `Erdos64EG.Internal.allPairTokenRouting_terminal,
          `Erdos64EG.Internal.allPairTokenRouting_verified,
          `Erdos64EG.Internal.allPairTokenRouting_traceValid,
          `Erdos64EG.Internal.allPairTokenRouting_total,
          `Erdos64EG.Internal.allPairTokenRouting_noOvercounting,
          `Erdos64EG.Internal.allPairTokenRouting_freeHandoff,
          `Erdos64EG.Internal.allPairTokenRouting_blockedHandoff,
          `Erdos64EG.Internal.allPairTokenRouting_checks,
          `Erdos64EG.Internal.allPairTokenRouting_checks_polynomial,
          `Erdos64EG.Internal.allPairTokenRouting_tokenCount_le_vertexCount,
          `Erdos64EG.Internal.allPairTokenRouting_checks_cubic,
          `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix
        ]
      }]
      scopeNotes := "This completes node [131] locally: the five-role executable dispatch and every assertion about a free-anchor fibre are verified. Its blocked output and free-anchor output are the exact green inputs consumed by the following capacity-token stage."
      workBound := "The generic graph contract has a 5n^6 worst-case bound. On this exact sparse residual, node [126] implies at most n selected-port tokens, hence at most n^2 pairs; Lean proves the sharper complete bound 5n^3. It never materializes Boolean states, graphs, contexts, paths, subgraphs, or recursive search trees."
    },
    {
      stepId := "erdos.blocked-capacity-token-ledger"
      stageId? := some "proof-slice.capacity-token-ledger"
      title := "Blocked-pair capacity-token and join ledger"
      plainExplanation := "This CT9 block consumes the exact blocked subtype and canonical first-hit payload emitted at node [132]. The admitted candidate type proves the raw quotient-audit exits impossible at node [133]. Every blocked pair is then retokenized by the deterministic window/remainder/primitive priority map at node [134], the selected P13 packing proves the exact window-join identity at node [135], and the result joins the verified free-anchor fibres in one exact 25-role partition at node [136]."
      formalStatement := "\\Pi_{\\rm blk}=\\bigsqcup_{t,r}\\Pi^{\\rm blk}_{t,r},\\qquad \\binom{|\\mathcal A_0|}{2}=\\sum_{t,r}\\widehat\\ell(t,r)"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "lem:sparse-pair-dependence-exit", title := "Sparse pair audit exits", nodeIds := [133] },
        { label := "def:canonical-blocker-ledger", title := "Canonical blocker ledger", nodeIds := [134] },
        { label := "def:capacity-token-ledger", title := "Capacity tokens for blocked pairs", nodeIds := [134, 136] },
        { label := "lem:exact-window-join-identity", title := "Exact window-join pressure", nodeIds := [135] },
        { label := "lem:token-ledger-no-overcount", title := "Exact blocked token partition", nodeIds := [136] },
        { label := "def:total-surplus-pair-token-route", title := "Completed blocked/free capacity-token map", nodeIds := [136] },
        { label := "lem:total-pair-token-route-no-overcount", title := "Complete capacity-token partition", nodeIds := [136] }
      ]
      declarationGroups := [{
        groupId := "capacity-token-ledger-ct9"
        title := "Framework-owned capacity-token refinement"
        role := .semanticTheorem
        explanation := "The graph layer owns the exact window, remainder-surplus, and primitive token sum; the deterministic blocked-pair priority; the 25-role relabelling of the unchanged source pair collection; and the polynomial work audit. The Erdős layer supplies only the selected minimal context and its already verified sparse bounds."
        declarations := [
          `Erdos64EG.Internal.exists_verifiedAllPairTokenRoutingPrefix,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.tokens_card_eq_fifteen_mul_packing_add_surplus,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.input_items_eq_source,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.free_token,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.blocked_token,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.noOvercounting,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.token_supply_exact,
          `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.verifiedStage,
          `Erdos64EG.Internal.capacityTokenActivationStage,
          `Erdos64EG.Internal.sparsePairAuditExit_closed,
          `Erdos64EG.Internal.canonicalBlockedToken_total,
          `Erdos64EG.Internal.exactWindowJoinIdentity,
          `Erdos64EG.Internal.capacityTokenSupply_exact,
          `Erdos64EG.Internal.totalCapacityLedger_noOvercounting,
          `Erdos64EG.Internal.totalCapacityRoleCount,
          `Erdos64EG.Internal.capacityLedgerChecks_cubic,
          `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix
        ]
      }]
      scopeNotes := "Nodes [133]--[136] are complete node-local contracts. Their sole predecessor is the green complete-pair dispatch at nodes [130]--[132]. The geometric overload audits are not used here."
      workBound := "The selected window ledger uses at most 13n² checks, and the complete token--role audit uses at most 225n³ comparisons. It scans only the existing pair, token, path-window, vertex, dart, and surplus-slot lists."
    },
    {
      stepId := "erdos.coupled-class-overload"
      stageId? := some "proof-slice.coupled-class-overload"
      title := "Exact 25-role coupled overload and class route"
      plainExplanation := "Nodes [137]--[139] and [141] execute one coupled CT9 contract on the exact node-[136] pair ledger. Positive exact excess returns a concrete overloaded token--role fibre. Its literal token constructor routes it uniquely through the window test and then the remainder test. On the other arithmetic side, the complete pair count, the nine-n token bound, and the exact identity 2 choose(σ,2)+σ=σ² prove the explicit node-[138] quadratic surplus bound."
      formalStatement := "D_{25}>0\\Rightarrow\\exists(t,r),\\ \\widehat\\ell(t,r)>b_{C(t)};\\qquad D_{25}=0\\Rightarrow\\sigma^2\\le(450b_{\\max}+1)n"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:exact-25-role-coupled-decision", title := "Exact 25-role coupled CT9 decision", nodeIds := [137, 138, 139, 141] }
      ]
      declarationGroups := [{
        groupId := "coupled-class-overload-ct9"
        title := "Reusable classwise token-capacity decision"
        role := .semanticTheorem
        explanation := "The generic CT9 profile owns exact product labels, total capacity, the overloaded-fibre residual, the aggregate within-capacity alternative, partition equality, and finite work. The graph specialization supplies only token classes and matching--star capacity numbers; the Erdős layer derives the selected graph's explicit quadratic bound."
        declarations := [
          `Erdos64EG.Internal.exists_verifiedCapacityTokenPrefix,
          `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.decide,
          `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.exactPartition,
          `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.totalCapacity_le,
          `StructuralExhaustion.Graph.SurplusClasswiseOverload.exactPartition,
          `StructuralExhaustion.Graph.SurplusClasswiseOverload.routeClass,
          `StructuralExhaustion.Graph.SurplusClasswiseOverload.routedOverload,
          `StructuralExhaustion.Graph.SurplusClasswiseOverload.totalCapacity_le,
          `StructuralExhaustion.Graph.SurplusClasswiseOverload.verifiedStage,
          `Erdos64EG.Internal.coupledClassProfile,
          `Erdos64EG.Internal.coupledExcess_positive_iff,
          `Erdos64EG.Internal.coupledOverloadClassRoute,
          `Erdos64EG.Internal.coupledPairCount_eq_chooseSurplus,
          `Erdos64EG.Internal.withinCoupledCapacity_pairBound,
          `Erdos64EG.Internal.noCoupledOverload_quadraticSpine,
          `Erdos64EG.Internal.coupledClassChecks_cubic,
          `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix
        ]
      }]
      scopeNotes := "These four decision/routing nodes are complete and consume only green node [136]. Nodes [140], [142], and [143] require the separate geometric matching--star audit and are not claimed by this stage."
      workBound := "At most 225n³ finite label comparisons on one selected graph. No Boolean state cube, graph family, matching family, path family, or recursive universe is materialized."
    },
    {
      stepId := "erdos.homogeneous-geometric-audits"
      stageId? := some "proof-slice.homogeneous-pattern"
      title := "Homogeneous geometric token audits"
      plainExplanation := "The exact overloaded fibre returned at node [137] is scanned by a deterministic greedy maximal matching. Nodes [139] and [141] select the threshold belonging to its literal token constructor, and the sharp endpoint-star count proves a matching or star of that size in the same fibre."
      formalStatement := "\\widehat\\ell(t,r)>(L_C-1)(2L_C-3)\\Longrightarrow\\text{an }L_C\\text{-matching or }L_C\\text{-star}"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "lem:same-token-matching-star", title := "Same-token matching--star bound", nodeIds := [140, 142, 143] }
      ]
      declarationGroups := [{
        groupId := "homogeneous-pattern-ct9"
        title := "Framework-owned greedy matching--star extraction"
        role := .semanticTheorem
        explanation := "The core layer owns the greedy scan, maximal coverage, endpoint-star charging, sharp cap, exact pattern certificate, and quadratic work audit. The graph layer projects only the selected CT9 fibre and routes its literal token class."
        declarations := [
          `StructuralExhaustion.Core.GreedyMatchingStar.greedy,
          `StructuralExhaustion.Core.GreedyMatchingStar.greedy_pairwise,
          `StructuralExhaustion.Core.GreedyMatchingStar.greedy_covers,
          `StructuralExhaustion.Core.GreedyMatchingStar.exists_pattern_of_cap_lt_card,
          `StructuralExhaustion.Core.GreedyMatchingStar.verifiedStage,
          `StructuralExhaustion.Graph.SurplusHomogeneousPattern.audit,
          `Erdos64EG.Internal.exists_verifiedCoupledClassOverloadPrefix,
          `Erdos64EG.Internal.homogeneousPatternAudit,
          `Erdos64EG.Internal.exists_verifiedHomogeneousPatternPrefix
        ]
      }]
      scopeNotes := "Nodes [140], [142], and [143] are complete: each consumes only the green overloaded-fibre residual selected by nodes [139] and [141]. The geometric routing-germ discharge at node [144] is separate and remains the frontier."
      workBound := "At most three times the square of the actual fibre length in pair-intersection and incidence tests. No matching family, star family, pair universe, graph family, path family, or context family is enumerated."
    },
    {
      stepId := "erdos.same-token-coarse-classification"
      stageId? := some "proof-slice.coarse-bottleneck-classification"
      title := "Fixed same-token coarse bottleneck classification"
      plainExplanation := "The classifier consumes the exact overloaded homogeneous pattern from node [140], [142], or [143]. A deterministic 48-code scan of its literal 49 pairs returns the first actual collision, retains exact attachment maps and two canonical rooted germs, and populates the registered semantic-consumer trigger."
      formalStatement := "|\\mathcal M|=49>48\\Longrightarrow\\exists x\\ne y,\\ c(x)=c(y)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-coarse-bottleneck-classification", title := "Fixed coarse bottleneck classification", nodeIds := [144] }
      ]
      declarationGroups := [{
        groupId := "same-token-coarse-collision"
        title := "Exact finite collision and typed germ residual"
        role := .semanticTheorem
        explanation := "The framework executes the literal finite-code decision, retains its run equality and exact graph provenance, constructs only the two selected germs, and routes the unchanged residual to its unique semantic consumer."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.verifiedCollision,
          `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.toSemanticBottleneckTrigger,
          `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_total,
          `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_source_exact,
          `Erdos64EG.Internal.coarseBottleneckClassification,
          `Erdos64EG.Internal.geometricCollisionChecks_eq,
          `Erdos64EG.Internal.geometricClassificationWork_eq,
          `Erdos64EG.Internal.exists_verifiedGeometricBottleneckClassificationPrefix
        ]
      }]
      scopeNotes := "Node [144] consumes only the exact green predecessor overload and homogeneous audit. It has no quadratic branch and does not assert attachment alignment, a sparse exit, Type B entry, CT3 response equivalence, or the near-cubic spine. Its exact trigger is consumed by the verified finite classifier at node [177]; the stronger semantic obligations remain isolated at white node [178]."
      workBound := "For 49 literal pairs: 2401 comparisons, at most 4802 uncached coarse-code projections, and two rooted BFS/germ budgets. No path family, context family, quotient family, subgraph family, graph family, or coloring family is enumerated."
    },
    {
      stepId := "erdos.same-token-semantic-bottleneck"
      stageId? := some "proof-slice.semantic-bottleneck-classification"
      title := "Finite attachment and germ-shape classification"
      plainExplanation := "The classifier consumes node [144]'s exact typed collision. It scans the retained 78p attachment coordinates, returns the first actual mismatch or proves full coordinatewise alignment, and in the aligned case classifies the two stored rooted germs into one of four exact shapes."
      formalStatement := "\\text{node-[144] trigger}\\Longrightarrow\\text{mismatch or one of four aligned germ shapes}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-semantic-bottleneck-classification", title := "Finite semantic-bottleneck classification", nodeIds := [177] },
        { label := "rem:same-token-semantic-bottleneck-classification-scope", title := "Semantic-classifier scope", nodeIds := [177] }
      ]
      declarationGroups := [{
        groupId := "same-token-semantic-classification"
        title := "Exact local alignment and five-way CT10 residual"
        role := .semanticTheorem
        explanation := "The core layer decides equality over a supplied finite coordinate list; the graph layer classifies only node [144]'s two retained attachment maps and rooted germs, and CT10 retains the unique accepted tag, verified trace, exact provenance, and linear work certificate."
        declarations := [
          `StructuralExhaustion.Core.FinitePredicateAlignment.Profile.decide,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify_source_exact,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classify_total,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run_verified,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.ct10Run_trace_valid,
          `StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck.classificationWork_le_vertices,
          `Erdos64EG.Internal.semanticBottleneckClassification,
          `Erdos64EG.Internal.semanticBottleneck_residual_exact,
          `Erdos64EG.Internal.semanticBottleneck_source_exact,
          `Erdos64EG.Internal.semanticBottleneck_germ_source_exact,
          `Erdos64EG.Internal.semanticBottleneck_ct10_verified,
          `Erdos64EG.Internal.semanticBottleneckClassificationWork_le_vertices,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckClassificationPrefix,
          `StructuralExhaustion.Graph.SurplusPatternCoarseRouting.semanticBottleneckTrigger_source_exact
        ]
      }]
      scopeNotes := "Node [177] proves only the exhaustive finite mismatch/alignment and four-shape classification. It does not turn any leaf into a sparse exit, CT3 response equivalence, decorated Type B handoff, fixed cap, or near-cubic spine; those implications remain at white node [178]."
      workBound := "Exactly 234p+7 primitive checks, bounded by 234|V|+7: three local predicate comparisons per one of 78p retained coordinates and seven CT10 table checks. No ambient path, context, quotient, subgraph, graph, coloring, or universe is enumerated."
    },
    {
      stepId := "erdos.same-token-semantic-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-local-consumer"
      title := "Local semantic-bottleneck separator split"
      plainExplanation := "Node [178] consumes all five exact node-[177] leaves. Mismatch and prefix leaves remain unchanged; root and after-edge divergence expose literal distinct incidences and branch only on the locally computed separator degree."
      formalStatement := "\\text{node-[177] leaf}\\Longrightarrow\\text{retained leaf or cubic/high local separator}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-local-semantic-consumer", title := "Local semantic-bottleneck separator split", nodeIds := [178] }
      ]
      declarationGroups := [{
        groupId := "same-token-local-consumer-total"
        title := "Exact five-leaf consumer and local separator degree"
        role := .semanticTheorem
        explanation := "The graph classifier retains the exact mismatch/prefix tags, extracts literal distinct incidences from divergent rooted germs, scans the actual ordered neighbour row only when a third incidence is needed, and proves the exhaustive frontier."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.classify,
          `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.classify_total,
          `StructuralExhaustion.Graph.SurplusPatternSemanticConsumer.checks_le_linear,
          `Erdos64EG.Internal.semanticBottleneckLocalConsumer,
          `Erdos64EG.Internal.semanticBottleneckLocalConsumer_previous_exact,
          `Erdos64EG.Internal.semanticBottleneckLocalConsumer_frontier_exact,
          `Erdos64EG.Internal.semanticBottleneckLocalConsumer_total,
          `Erdos64EG.Internal.semanticBottleneckLocalConsumer_checks_le_vertices,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalConsumerPrefix
        ]
      }]
      scopeNotes := "Node [178] proves no sparse exit, CT3 response equivalence, decorated Type B handoff, fixed cap, or near-cubic spine. Those stronger implications remain white node [181]."
      workBound := "At most |V|+1 local incidence/degree checks. No path, context, quotient, subgraph, graph, coloring, or universe family is enumerated."
    },
    {
      stepId := "erdos.same-token-geometric-closure-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-switch-normalization"
      title := "Cubic switch normalization"
      plainExplanation := "Node [181] consumes node [178] exactly. Cubic divergence leaves become literal four-vertex cubic-star data; high leaves retain degree at least four, and mismatch/prefix leaves pass through unchanged."
      formalStatement := "\\text{node-[178] frontier}\\Longrightarrow\\text{literal cubic star or retained residual}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-cubic-switch-normalization", title := "Cubic switch normalization", nodeIds := [181] }
      ]
      declarationGroups := [{
        groupId := "same-token-switch-normalization-total"
        title := "Exact seven-way normalized frontier"
        role := .semanticTheorem
        explanation := "The graph layer repackages only already proved incidences and degree branches. The application proves exact node-[178] provenance, result equality, totality, and zero new checks."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.normalize,
          `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.normalize_total,
          `StructuralExhaustion.Graph.SurplusPatternSemanticNormalization.checks_eq_zero,
          `Erdos64EG.Internal.semanticBottleneckNormalizationSource_node178_exact,
          `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_result_exact,
          `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_total,
          `Erdos64EG.Internal.semanticBottleneckSwitchNormalization_checks_eq_zero,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckSwitchNormalizationPrefix
        ]
      }]
      scopeNotes := "Node [181] proves no sparse exit, CT3 equivalence, Type B handoff, fixed cap, or near-cubic spine; those remain white node [184]."
      workBound := "Zero new primitive checks; no ambient family is enumerated."
    },
    {
      stepId := "erdos.same-token-normalized-geometric-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-local-projection"
      title := "Local separator projection"
      plainExplanation := "Node [184] consumes node [181] exactly, projecting cubic leaves to literal switch-boundary support and high leaves to their declared local port rows."
      formalStatement := "\\text{node-[181]}\\Longrightarrow\\text{switch boundary or high-port row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-local-separator-projection", title := "Local separator projection", nodeIds := [184] }]
      declarationGroups := [{
        groupId := "same-token-local-projection"
        title := "Exact cubic/high projection"
        role := .semanticTheorem
        explanation := "All seven node-[181] leaves are retained with literal local support and port cardinality."
        declarations := [
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.project,
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.project_total,
        `StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection.visibleChecks_linear,
        `Erdos64EG.Internal.semanticBottleneckLocalProjectionSource_node181_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_projection_exact,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_total,
        `Erdos64EG.Internal.semanticBottleneckLocalProjection_visibleChecks_linear,
        `Erdos64EG.Internal.exists_verifiedSemanticBottleneckLocalProjectionPrefix
      ] }]
      scopeNotes := "Node [184] proves no sparse exit, response equality, CT3, Type B, fixed cap, fan safety, or target closure; those remain white node [187]."
      workBound := "At most |V| local declared-port checks."
    },
    {
      stepId := "erdos.same-token-local-projection-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-strong-frontier"
      title := "Strong-semantic obligation frontier"
      plainExplanation := "Node [187] retains every exact node [184] payload and tags it with the next required theorem: sparse exit, fixed caps, CT3, or Type B. The tags are not certificates."
      formalStatement := "\\text{node-[184] leaf}\\Longrightarrow\\text{retained payload with pending obligation tag}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-strong-semantic-obligation-frontier", title := "Strong-semantic obligation frontier", nodeIds := [187] }]
      declarationGroups := [{
        groupId := "same-token-strong-obligation-frontier"
        title := "Exact seven-leaf obligation tagging"
        role := .semanticTheorem
        explanation := "The classifier retains the exact projected payload and records only its required downstream theorem. The application proves node-[184] equality, retention, totality, and constant local work."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify,
          `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_total,
          `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_retains,
          `StructuralExhaustion.Graph.SurplusPatternStrongSemanticFrontier.classify_obligation_exact,
          `Erdos64EG.Internal.semanticBottleneckStrongFrontierSource_node184_exact,
          `Erdos64EG.Internal.semanticBottleneckStrongFrontier_pending_exact,
          `Erdos64EG.Internal.semanticBottleneckStrongFrontier_retains_node184,
          `Erdos64EG.Internal.semanticBottleneckStrongFrontier_total,
          `Erdos64EG.Internal.semanticBottleneckStrongFrontier_visibleChecks_constant,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckStrongFrontierPrefix
        ]
      }]
      scopeNotes := "Node [187] proves no sparse exit, CT3 equivalence, Type B handoff, or fixed cap; those remain white node [190]."
      workBound := "One constructor inspection; no ambient family is enumerated."
    },
    {
      stepId := "erdos.same-token-strong-semantic-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-first-clause"
      title := "First local separator clause"
      plainExplanation := "Node [190] retains node [187]'s exact payload and tag. Cubic leaves expose three exact boundary incidences; high leaves expose four distinct adjacent declared ports."
      formalStatement := "\\text{node-[187] payload}\\Longrightarrow\\text{fixed-arity literal separator data}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-first-local-separator-clause", title := "First local separator clause", nodeIds := [190] }]
      declarationGroups := [{
        groupId := "same-token-first-local-clause"
        title := "Exact fixed-arity incidence clause"
        role := .semanticTheorem
        explanation := "The graph certificate retains mismatch/prefix evidence and exposes only Fin 3 cubic boundary or the first four declared high ports."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.certify,
          `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.run,
          `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.run_total,
          `StructuralExhaustion.Graph.SurplusPatternFirstSemanticClause.visibleChecks_constant,
          `Erdos64EG.Internal.semanticBottleneckFirstClauseSource_node187_exact,
          `Erdos64EG.Internal.semanticBottleneckFirstClause_result_exact,
          `Erdos64EG.Internal.semanticBottleneckFirstClause_obligation_exact,
          `Erdos64EG.Internal.semanticBottleneckFirstClause_total,
          `Erdos64EG.Internal.semanticBottleneckFirstClause_visibleChecks_constant,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckFirstClausePrefix
        ]
      }]
      scopeNotes := "Node [190] discharges no sparse-exit, CT3, Type B, fixed-cap, response, or target conclusion; node [193] records the terminal pairwise-clause residual."
      workBound := "At most four literal local positions."
    },
    {
      stepId := "erdos.same-token-first-clause-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-pairwise-clause"
      title := "Pairwise local separator clause"
      plainExplanation := "Node [193] preserves node [190] and the pending obligation exactly, deriving only pairwise boundary or endpoint inequalities from the retained fixed-arity local data."
      formalStatement := "\\text{node-[190] local clause}\\Longrightarrow\\text{pairwise local inequalities plus unchanged residual}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-pairwise-local-separator-clause", title := "Pairwise local separator clause", nodeIds := [193] }]
      declarationGroups := [{
        groupId := "same-token-pairwise-local-clause"
        title := "Pairwise fixed-arity separator facts"
        role := .semanticTheorem
        explanation := "The local graph layer derives pairwise distinctness and center-to-boundary inequalities; the application proves exact node-[190] and pending-obligation provenance."
        declarations := [
          `StructuralExhaustion.Graph.LocalSeparatorPairwiseClause.cubic,
          `StructuralExhaustion.Graph.LocalSeparatorPairwiseClause.high,
          `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.run,
          `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.run_total,
          `StructuralExhaustion.Graph.SurplusPatternPairwiseSemanticClause.visibleChecks_eq_zero,
          `Erdos64EG.Internal.semanticBottleneckPairwiseClauseSource_node190_exact,
          `Erdos64EG.Internal.semanticBottleneckPairwiseClause_result_exact,
          `Erdos64EG.Internal.semanticBottleneckPairwiseClause_obligation_exact,
          `Erdos64EG.Internal.semanticBottleneckPairwiseClause_total,
          `Erdos64EG.Internal.semanticBottleneckPairwiseClause_visibleChecks_eq_zero,
          `Erdos64EG.Internal.exists_verifiedSemanticBottleneckPairwiseClausePrefix
        ]
      }]
      scopeNotes := "This terminal interface does not prove sparse exit, CT3 equivalence, Type B handoff, fixed cap, response semantics, or target closure."
      workBound := "Zero visible checks; fixed-arity facts only."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "erdos-64"
  title := "Erdős Problem 64"
  summary :=
    "A partial proof with exact Mersenne returns, lexicographic minimal selection, CT2 criticality and bridge contraction, CT3 boundaried uncompressibility, an HSS-forced induced-P13 CT1 stage, a routed maximum-packing CT12 remainder stage, the complete CT10 P13 attachment-label algebra, a polynomial ordered CT6 degree-surplus ledger with exact per-slot activation, the CT15 baseline and free/blocked pair-response stages, the exact CT9 capacity-token partition, and the exact 25-role coupled overload/class decision, together with the framework-native local-port and Type B ledgers retained by the same selected graph."
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
      bindingId := "proof-slice.ct15-baseline-spine-demand"
      stageId := "proof-slice.baseline-spine-demand"
      tacticId := "CT15"
      role := "certified finite baseline demand"
      description := "The application supplies the exact cubic-baseline count and a concrete independently target-testable coordinate family with its deficit. The framework computes full rank, the unit-charge ledger, terminal, trace, soundness, totality, and a linear check budget."
      problemDeclaration := `Erdos64EG.Internal.baselineSpineProfile
      frameworkDeclaration :=
        `StructuralExhaustion.CT15.BaselineDemand.Profile.verifiedStage
    },
    {
      bindingId := "proof-slice.ct15-sparse-pair-responses"
      stageId := "proof-slice.sparse-pair-responses"
      tacticId := "CT15"
      role := "audited exact free-pair response rank"
      description := "The application passes the exact activated schedule. The reusable core and graph layers generate the pair partition, retain local blockers and shortest connectors, audit raw quotient proposals, rule out non-injective admitted quotients by certified minimality reduction, and execute CT15 on exactly the free coordinates."
      problemDeclaration := `Erdos64EG.Internal.sparsePairResponseStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.SurplusPairResponse.verifiedStage
    },
    {
      bindingId := "proof-slice.ct9-total-pair-token-route"
      stageId := "proof-slice.total-pair-token-route"
      tacticId := "CT9"
      role := "exact local token--role dispatch"
      description := "The application consumes the exact pair split. The reusable CT9 product ledger partitions every scheduled pair once; the graph route proves that freeAnchor is precisely the negative blocker branch and that blocked pairs retain the canonical first hit."
      problemDeclaration := `Erdos64EG.Internal.allPairTokenRoutingInput
      frameworkDeclaration :=
        `StructuralExhaustion.CT9.TokenRoleLedger.noOvercounting
    },
    {
      bindingId := "proof-slice.ct9-capacity-token-ledger"
      stageId := "proof-slice.capacity-token-ledger"
      tacticId := "CT9"
      role := "exact capacity-token refinement"
      description := "The application supplies the already verified pair split and sparse graph bounds. The graph layer constructs the disjoint window/remainder/primitive token universe, retokenizes the blocked side by deterministic priority, preserves the free-anchor side, and proves the exact 25-role partition and cubic work bound."
      problemDeclaration := `Erdos64EG.Internal.capacityTokenActivationStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.SurplusCapacityTokenRouting.verifiedStage
    },
    {
      bindingId := "proof-slice.ct9-coupled-class-overload"
      stageId := "proof-slice.coupled-class-overload"
      tacticId := "CT9"
      role := "exact classwise capacity decision"
      description := "The application supplies only the fixed threshold triple and the preceding verified stage. The reusable CT9 contract compares the literal complete pair list with class capacities, returns a concrete overload or an aggregate bound, and the graph layer routes overloads by the literal token constructor."
      problemDeclaration := `Erdos64EG.Internal.coupledClassProfile
      frameworkDeclaration :=
        `StructuralExhaustion.CT9.ClasswiseTokenLedger.Profile.decide
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
