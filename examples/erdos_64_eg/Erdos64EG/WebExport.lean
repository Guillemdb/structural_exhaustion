import Erdos64EG
import Erdos64EG.Node53
import Erdos64EG.Future.P13Node24To26
import Erdos64EG.Future.P13Node27To28
import Erdos64EG.Future.P13Node28To29
import Erdos64EG.Future.P13Node29To30
import Erdos64EG.Future.P13Node30To31
import Erdos64EG.Future.P13Node31To32
import Erdos64EG.Future.P13Node32To33
import Erdos64EG.Future.P13Node32To34
import Erdos64EG.Future.P13Node33To35
import Erdos64EG.Future.P13Node35To36
import Erdos64EG.Future.P13Node36To37
import Erdos64EG.Future.P13Node36To38
import Erdos64EG.Future.P13Node38To39
import Erdos64EG.Future.P13Nodes35To47Refinement
import Erdos64EG.Future.P13Nodes47To51Refinement
import Erdos64EG.Future.P13Node24AsymptoticTransport
import StructuralExhaustion.Canonical.ExampleExport
import StructuralExhaustion.CT15.FunctionalAdmissibleRank

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
        `Erdos64EG.Internal.localTransition_not_enabled,
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
      summary := "Node [15] makes the exhaustive P₁₃-free decision on the literal node-[14] stage; node [16] closes exactly its yes constructor with HSS and retains the literal no constructor."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode16
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle,
        `Erdos64EG.Internal.Node15Stage,
        `Erdos64EG.Internal.node15P13Decision,
        `Erdos64EG.Internal.node15_exhaustive,
        `Erdos64EG.Internal.runInitialThroughNode15,
        `Erdos64EG.Internal.node15LocalChecks_eq_zero,
        `Erdos64EG.Internal.hssTarget_of_p13Free,
        `Erdos64EG.Internal.node16_hss_target,
        `Erdos64EG.Internal.node16_hss_closure,
        `Erdos64EG.Internal.Node16Stage,
        `Erdos64EG.Internal.node16HSSContinuation,
        `Erdos64EG.Internal.runInitialThroughNode16,
        `Erdos64EG.Internal.node16LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-packing"
      title := "CT12 induced-P₁₃ packing"
      summary := "Node [17] selects a deterministic maximal vertex-disjoint induced-P₁₃ family and retains CT12 disjointness, saturation, terminal, trace, totality, nonemptiness, and local work evidence."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode17
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node17Stage,
        `Erdos64EG.Internal.Node17Output,
        `Erdos64EG.Internal.Node17StageContext,
        `Erdos64EG.Internal.node17Windows,
        `Erdos64EG.Internal.node17PackingNumber,
        `Erdos64EG.Internal.node17InducedP13Packing,
        `Erdos64EG.Internal.runInitialThroughNode17,
        `Erdos64EG.Internal.node17_maximal,
        `Erdos64EG.Internal.node17_terminal,
        `Erdos64EG.Internal.node17Total,
        `Erdos64EG.Internal.node17WorkBudget,
        `Erdos64EG.Internal.node17_nonempty
      ]
    },
    {
      stageId := "proof-slice.p13-labels"
      title := "CT10 P₁₃ attachment-label algebra"
      summary := "One CT10 stage classifies every nonempty attachment label on the fixed thirteen-position path, certifies the exact 399-row table and size distribution, and defines the manuscript compatibility and two-step curvature relations."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.node18P13LabelAlgebra
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13CodeLegal_iff_gapLegal,
        `Erdos64EG.Internal.p13Legal_iff_gapLegal,
        `Erdos64EG.Internal.P13ParityLabelCount.gapSafeSized13_natCard_eq_convolution,
        `Erdos64EG.Internal.P13ParityLabelCount.gapLegal13_natCard,
        `Erdos64EG.Internal.symbolicLegalP13Labels_card,
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
        `Erdos64EG.Internal.Node18Stage,
        `Erdos64EG.Internal.Node18Output,
        `Erdos64EG.Internal.Node18Output.actualLabelsLegal,
        `Erdos64EG.Internal.Node18StageContext,
        `Erdos64EG.Internal.node18P13LabelAlgebra,
        `Erdos64EG.Internal.runInitialThroughNode18,
        `Erdos64EG.Internal.node18LocalChecks_eq
      ]
    },
    {
      stageId := "proof-slice.surplus-scale-split"
      title := "Exact quadratic surplus-scale split"
      summary := "The actual degree surplus is compared with the squared fixed homogeneous-cap scale by one natural-number comparison, giving the exhaustive node-[19] non-near-cubic or bounded branch."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode19
      evidenceDeclarations := [
        `Erdos64EG.Internal.node19SurplusCoefficient,
        `Erdos64EG.Internal.node19Profile,
        `Erdos64EG.Internal.node19Family,
        `Erdos64EG.Internal.Node19High,
        `Erdos64EG.Internal.Node19Low,
        `Erdos64EG.Internal.Node19Stage,
        `Erdos64EG.Internal.node19SurplusScaleDecision,
        `Erdos64EG.Internal.runInitialThroughNode19,
        `Erdos64EG.Internal.node19_exhaustive,
        `Erdos64EG.Internal.node19WorkBudget,
        `Erdos64EG.Internal.node19_work_zero,
        `Erdos64EG.Internal.Node20Entry,
        `Erdos64EG.Internal.Node20SourceStage,
        `Erdos64EG.Internal.node20Entry_iff_node19High,
        `Erdos64EG.Internal.node20LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-node25-large-remainder"
      title := "Node [25] exact Residual A"
      summary := "The literal node-[24] active cursor is mapped to the canonical CT12 packing complement, its exact partition and scaled largeness, and hereditary induced-P13-freeness."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode25
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node25Remainder,
        `Erdos64EG.Internal.Node25Output,
        `Erdos64EG.Internal.Node25Stage,
        `Erdos64EG.Internal.node25P13LargeRemainder,
        `Erdos64EG.Internal.node25LocalChecks_eq_zero,
        `StructuralExhaustion.Core.DensityAsymptoticTransport.nat_partition_complement_lower,
        `Erdos64EG.Internal.p13Remainder_partition,
        `Erdos64EG.Internal.p13Remainder_free,
        `Erdos64EG.Internal.p13Remainder_componentwise_free
      ]
    },
    {
      stageId := "proof-slice.p13-node26-remainder-continuation"
      title := "Node [26] Residual A panel continuation"
      summary := "The framework maps the literal node-[25] output and records only that the Part-II remainder name is the same canonical packing complement."
      kind := .adapter
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode26
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node26Output,
        `Erdos64EG.Internal.Node26Stage,
        `Erdos64EG.Internal.node26P13RemainderContinuation,
        `Erdos64EG.Internal.node26LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
      ]
    },
    {
      stageId := "proof-slice.p13-node27-no-three-core"
      title := "Node [27] no internal three-core"
      summary := "On the exact node-[26] remainder, the existing graph lemmas exclude both an induced internal minimum-degree-three support and the manuscript's stronger finite internal subgraph form."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode27
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node27Output,
        `Erdos64EG.Internal.Node27Stage,
        `Erdos64EG.Internal.node27P13NoInternalThreeCore,
        `Erdos64EG.Internal.node27LocalChecks_eq_zero,
        `Erdos64EG.Internal.p13Remainder_internalThreeCore_free,
        `Erdos64EG.Internal.p13Remainder_internalSubgraphThreeCore_free
      ]
    },
    {
      stageId := "proof-slice.p13-positive-deficiency"
      title := "Exact P13-remainder positive deficiency"
      summary := "Node [28] maps the literal node-[27] cursor and records exactly the graph-owned positive-deficiency sum on that unchanged remainder."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode28
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.internalDegree,
        `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.positiveDeficiency,
        `Erdos64EG.Internal.p13RemainderDeficiencyProfile,
        `Erdos64EG.Internal.p13Remainder_positiveDeficiency_eq,
        `Erdos64EG.Internal.Node28Output,
        `Erdos64EG.Internal.Node28Stage,
        `Erdos64EG.Internal.node28P13PositiveDeficiency,
        `Erdos64EG.Internal.node28LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-external-incidence-supply"
      title := "Exact external-incidence supply"
      summary := "The literal node-[28] remainder deficiency injects into its R--W boundary incidences, those incidences embed in the selected-window token schedule, and the exact schedule identity gives 15p13+sigma_W together with its surplus-adjusted form."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode29
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node29Output,
        `Erdos64EG.Internal.Node29Stage,
        `Erdos64EG.Internal.node29P13ExternalIncidenceSupply,
        `Erdos64EG.Internal.node29LocalChecks_eq_zero,
        `Erdos64EG.Internal.p13Curvature_positiveDeficiency_eq_previous,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.positiveDeficiency_le_boundaryIncidences,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.checks_le_thirteen_mul_square
      ]
    },
    {
      stageId := "proof-slice.p13-wedge-lower"
      title := "Exact remainder wedge lower bound"
      summary := "The graph-owned degree-count identity is applied to every supplied finite component support and to the exact remainder. Node [29]'s incidence supply gives the finite window-only error, while the reusable real transport handles both manuscript rates without scanning another universe."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode30
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node30Output,
        `Erdos64EG.Internal.Node30Stage,
        `Erdos64EG.Internal.node30P13WedgeLower,
        `Erdos64EG.Internal.node30LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.three_mul_card_le_wedgeCount_add_twice_deficiency,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeFloor,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeRate_of_deficiencyRate,
        `Erdos64EG.Internal.p13Remainder_wedgeFloor,
        `Erdos64EG.Internal.p13Node30OmegaWindow,
        `Erdos64EG.Internal.p13Node30OmegaWindow_gt_printed
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-target-rank"
      title := "Exact curvature target-rank definition"
      summary := "The literal raw remainder wedges and their cardinality are verified. The public node value is the attained maximum over the graph-owned carrier/proposal/realization/admissibility/functionality universe, with exact W2(R) upper bound and no enumeration of quotient or realization families."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode31
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node31Output,
        `Erdos64EG.Internal.Node31Stage,
        `Erdos64EG.Internal.node31P13CurvatureTargetRank,
        `Erdos64EG.Internal.node31LocalChecks_eq_zero,
        `Erdos64EG.Internal.p13CurvatureCoordinates,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_eq_wedgeCount,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_le_cube,
        `Erdos64EG.Internal.p13CurvatureResponseProfile,
        `Erdos64EG.Internal.p13CurvatureFunctionalRankProfile,
        `Erdos64EG.Internal.p13CurvatureTargetRank,
        `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.targetRank_le_coordinates
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-rank-decision"
      title := "Exact curvature rank-loss dichotomy"
      summary := "The exact node-[31] maximum is compared with the complete raw wedge cardinality. The two original edges are exhaustive: strict rank loss, or equality with the full schedule. This proof-level comparison evaluates no family of subfamilies, quotients, or contexts."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode32
      evidenceDeclarations := [
        `Erdos64EG.Internal.node32RankDecision,
        `Erdos64EG.Internal.Node32RankDrop,
        `Erdos64EG.Internal.Node32FullRank,
        `Erdos64EG.Internal.Node32Stage,
        `Erdos64EG.Internal.node32P13RankDropDecision,
        `Erdos64EG.Internal.node32LocalChecks_eq_zero,
        `Erdos64EG.Internal.node32RankDecision_exhaustive,
        `Erdos64EG.Internal.node32RankDecisionWork_eq_zero,
        `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision,
        `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision_exhaustive
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-dependence-open"
      title := "Node [33] rank-reducing branch marker"
      summary := "Node [33] names only node [32]'s literal strict-rank-loss constructor as a PUnit branch marker. The decision proof remains at node [32], and circuit extraction belongs to node [35]."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode33
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node33Output,
        `Erdos64EG.Internal.Node33Stage,
        `Erdos64EG.Internal.node33P13RankReducingBranch,
        `Erdos64EG.Internal.node33LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionYes
      ]
    },
    {
      stageId := "proof-slice.p13-full-curvature-rank"
      title := "Exact full-curvature-rank residual"
      summary := "Node [34] names only node [32]'s literal full-rank constructor as a PUnit branch marker. The exact equality remains in the node-[32] decision payload and is not copied into a new application record."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode34
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node34Output,
        `Erdos64EG.Internal.Node34Stage,
        `Erdos64EG.Internal.node34P13FullRankResidual,
        `Erdos64EG.Internal.node34LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionNo
      ]
    },
    {
      stageId := "proof-slice.p13-multiscale-curvature"
      title := "Node [21] multi-scale curvature interface"
      summary := "The lightweight node-[21] API fixes the exact 91-barrier output and literal node-[19] no-continuation type. Its optimized producer is still yellow, so later stages consume the same typed output provisionally without changing the paper edge."
      kind := .tactic
      tacticId? := some "CT10"
      primaryDeclaration :=
        `Erdos64EG.Internal.Node21Output
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13BarrierAccepted,
        `Erdos64EG.Internal.p13BarrierClassification,
        `Erdos64EG.Internal.p13MultiScaleBarrierProfile,
        `Erdos64EG.Internal.p13BarrierSafeCount,
        `Erdos64EG.Internal.p13BarrierFlatCount,
        `Erdos64EG.Internal.p13BarrierSafeProduct,
        `Erdos64EG.Internal.p13BarrierFlatProduct,
        `Erdos64EG.Internal.p13MultiScaleCheckCount,
        `Erdos64EG.Internal.Node21Context,
        `Erdos64EG.Internal.Node21Stage
      ]
    },
    {
      stageId := "proof-slice.p13-weighted-live-cold"
      title := "Weighted live/cold P₁₃ window interface"
      summary := "The exact packing is processed in order. A recoverable graph-semantic extension is accepted into the accumulated hot aggregate, or the identical window and prior aggregate are retained as a cold rejection. The sequential cold list is partitioned by ambient cubicity and routed to the thirteen-stub schedule."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.p13SequentialWeightedHotCount_add_coldCount
      evidenceDeclarations := [
        `StructuralExhaustion.Core.VariableConditionalFibreProductCost.Profile.complete_product_le,
        `StructuralExhaustion.Core.VariableConditionalFibreProductCost.Profile.checks_le_state_mul_coordinate,
        `Erdos64EG.Internal.P13WeightedLiveWindowPackage,
        `Erdos64EG.Internal.P13WeightedLiveWindowPackage.product_le,
        `Erdos64EG.Internal.P13WeightedLiveWindowPackage.checks_local,
        `Erdos64EG.Internal.P13WeightedHotWindow,
        `StructuralExhaustion.Core.SequentialCompatibleExtensionLedger.run,
        `Erdos64EG.Internal.P13SequentialHotAggregate,
        `Erdos64EG.Internal.P13SequentialCompatibleExtension,
        `Erdos64EG.Internal.P13SequentialWeightedColdWindow,
        `Erdos64EG.Internal.p13SequentialFinal_localProduct_le_fixedCapacity,
        `Erdos64EG.Internal.p13SequentialFinal_retainedCount,
        `Erdos64EG.Internal.p13SequentialWeightedColdWindows_window_nodup,
        `Erdos64EG.Internal.p13SequentialHotBudget_total_le_budget_add_cold,
        `Erdos64EG.Internal.p13WeightedCold_cubic_nonCubic_length,
        `Erdos64EG.Internal.p13WeightedColdNonCubic_length_le_totalSurplus,
        `Erdos64EG.Internal.p13WeightedColdNonCubic_length_sq_le_nearCubicBudget,
        `Erdos64EG.Internal.p13WeightedColdBranchExcessStubs_length,
        `Erdos64EG.Internal.p13WeightedColdBranchExcessStubs_nodup,
        `Erdos64EG.Internal.P13WeightedColdBranchExcessStub.sameWindow,
        `Erdos64EG.Internal.p13WeightedColdBranchExcessSchedule_length,
        `Erdos64EG.Internal.p13WeightedColdBranchExcessSchedule_nodup,
        `Erdos64EG.Internal.p13WeightedColdRestrictedEntries_sources,
        `Erdos64EG.Internal.p13WeightedColdRestrictedEntries_sources_nodup,
        `Erdos64EG.Internal.p13WeightedColdRestrictedComponentSchedule_sources,
        `Erdos64EG.Internal.p13WeightedColdRestrictedComponentSchedule_sources_nodup,
        `Erdos64EG.Internal.thirteen_mul_weightedCold_le_branchExcess_add_surplus,
        `Erdos64EG.Internal.verifiedP13WeightedColdNearCubicPayment,
        `Erdos64EG.Internal.P13WeightedColdBranchExcessStub.corridor
      ]
    },
    {
      stageId := "proof-slice.type-a-nodes57-63-local-provenance"
      title := "Nodes [57]--[63] dependency-indexed Type-A chain"
      summary := "Node [57] consumes the accumulated node-[56] cap on its genuine eventual tail. Nodes [58]--[60] retain the exact integer net charge, CT11 localizes a negative canonical component at node [61], and node [62] returns exactly the paper's Type-A or Type-B edge."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node57_eventually
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANodes57To63Provenance.strictQuarterNat_of_normalized,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node57Refinement,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node58Refinement,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node59Refinement,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node60_impossible,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node61Refinement,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node62,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.localChecks_linear
      ]
    },
    {
      stageId := "proof-slice.type-a-nodes86-88-local-thresholds"
      title := "Nodes [86]--[88] local Type-A thresholds"
      summary := "From a supplied exact node-[63] Type-A residual, the local chain proves zero assigned surplus, the strict quarter deficiency, the P13-free diameter-eleven Moore bound, and the three original receiver thresholds. It stays conditional on the yellow node-[63] predecessor."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node86
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.VerifiedNode86Residual.assignedSurplus_eq_zero,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.VerifiedNode86Residual.four_deficiency_lt_card,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_p13Free,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_diameterAtMostEleven,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_supportCardAtMost6142_of_diameter,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87Checks_polynomial,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.q,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.threshold,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node88,
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node88Checks_constant
      ]
    },
    {
      stageId := "proof-slice.type-a-node89-local-saturation"
      title := "Node [89] local receiver-saturation decision"
      summary := "On a supplied exact node-[88] residual, one finite receiver-fibre decision returns exactly the original no edge to [90] or yes edge to [93], with exact predecessor identity and polynomial local work. Node [89] remains dependency-blocked by node [88]."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.TypeANode89SaturationDecision.run
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANode89SaturationDecision.input,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.routing,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.routedReceiver_eq_canonical,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.ToNode93,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.ToNode90,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.run_exhaustive,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.localCheckCount_polynomial,
        `Erdos64EG.Internal.TypeANode89SaturationDecision.workBudget
      ]
    },
    {
      stageId := "proof-slice.p13-node153-produced-support-coverage"
      title := "Node [153] prior produced-support coverage"
      summary := "A framework-owned persistent ledger aggregates ordinary, decorated, and route-8 occurrences without deduplication. F4 recognizes and filters literal occurrences directly. The graph-owned global producers remain explicit upstream obligations."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.outside_all_produced_occurrences
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteResidualLedger.Ledger,
        `StructuralExhaustion.Core.ResidualRefinement.Ledger.append,
        `StructuralExhaustion.Core.ResidualRefinement.Ledger.require,
        `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.activeOccurrences,
        `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.activeOccurrences_card_le_occurrences,
        `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.recognize_exact,
        `StructuralExhaustion.Graph.ResidualSupportRefinement.Profile.recognize_exact,
        `StructuralExhaustion.Graph.ResidualSupportRefinement.Profile.FirstHit.get,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedger.PersistentLedger.recognize_exact,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.persistentBase,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.persistentBase_event_origin,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.CompleteState,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.ordinaryOccurrence_mem,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.decoratedOccurrence_mem,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.routeEightOccurrence_mem,
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_completeProducedLedger
      ]
    },
    {
      stageId := "proof-slice.p13-node153-exact-continuation"
      title := "Node [153] restricted corridor and exact local F2--F5 continuation"
      summary := "The existing component edge retains its actual component and lexicographically first simple corridor. Its stored literal stages are then scanned in the paper's F1, F2, F3, F4, F5 order. The prior-support connector preserves every occurrence supplied by the exact producer schedules; the upstream global ordinary/realization producer and ColdBoundedGerm producer remain absent."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.runExactContinuation
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.StageF2,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.StageF3,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.ExactF5,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.f4_absent,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.repeatedStageF2,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.repeatedStageF3,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactF5OfClear,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactLaterSemantics,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.runExactContinuation_total,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactContinuation_checks,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_isPath,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_head,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_getLast,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.no_earlier_path,
        `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_length_lt,
        `Erdos64EG.Internal.restricted_component_payload,
        `Erdos64EG.Internal.restricted_component_declaredOrderCorridor,
        `Erdos64EG.Internal.p13RestrictedLexFirstCorridorProfile,
        `Erdos64EG.Internal.p13RestrictedLexFirstCorridor,
        `Erdos64EG.Internal.restricted_component_lexFirstCorridor
      ]
    },
    {
      stageId := "proof-slice.p13-node154-local-classifier"
      title := "Node [154] local G1--G3 classifier"
      summary := "For one supplied bounded germ, the original priority classifier tests its literal hit first and, only when absent, scans the germ's declared finite response codes. The three outcomes are exhaustive with an exact local trace and a linear code-schedule work bound; this stage does not produce the bounded germ."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classify_exhaustive_with_trace
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FinitePriorityOptionScanWork.trace,
        `StructuralExhaustion.Core.FinitePriorityOptionScanWork.checks,
        `StructuralExhaustion.Core.FinitePriorityOptionScanWork.checks_le_codes_add_one,
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classify,
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyTrace,
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyTrace_length_le_three,
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyChecks,
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyChecks_le_codes_add_one
      ]
    },
    {
      stageId := "proof-slice.p13-node146-route8-threshold"
      title := "Node [146] route-8 density threshold"
      summary := "The framework attaches the canonical node-[145] ledger once. One exact comparison then decides 78 p13 < n and adds only the corresponding theta/tau arithmetic payload; both original outgoing states retain the complete accumulated ledger automatically."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.p13Node146AccumulatedRun
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13PackingTheta,
        `Erdos64EG.Internal.p13Route8Tau,
        `Erdos64EG.Internal.p13VertexCount_pos,
        `Erdos64EG.Internal.p13Route8BelowThreshold_iff_theta,
        `Erdos64EG.Internal.p13Route8Tau_lt_three_thirteenths_iff,
        `Erdos64EG.Internal.p13Route8_denominator_pos_of_below,
        `Erdos64EG.Internal.P13Node146To147,
        `Erdos64EG.Internal.P13Node146To148,
        `Erdos64EG.Internal.p13Node145LedgerRefinement,
        `Erdos64EG.Internal.p13Node146DecisionRefinement,
        `Erdos64EG.Internal.p13Node146To147Refinement,
        `Erdos64EG.Internal.p13Node146To148Refinement,
        `Erdos64EG.Internal.p13Node146LocalCheckCount_polynomial,
        `Erdos64EG.Internal.p13Node146WorkBudget,
        `Erdos64EG.Internal.p13Node146WorkBudget_checks
      ]
    },
    {
      stageId := "proof-slice.p13-node147-private-carrier-arithmetic"
      title := "Node [147] private-carrier arithmetic prefix"
      summary := "The framework-owned node-[146] yes state yields the strict numerical margin required by the route-8 carrier squeeze. CT4 now owns the private-carrier injection used at nodes [119]--[120]; the graph-semantic node-[109]--[114] route-8 entry/core producer remains missing, so node [147] stays partial."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.p13Node147ArithmeticRefinement
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Route8CollisionCoefficientGap,
        `Erdos64EG.Internal.p13Route8CollisionMargin_pos,
        `Erdos64EG.Internal.P13Node147ArithmeticPrefix,
        `Erdos64EG.Internal.p13Node147ArithmeticRefinement,
        `StructuralExhaustion.CT4.PrivateCarrierProfile.slot_mul_entry_le_carrier,
        `Erdos64EG.Internal.P13Route8PrivateCarrierLedger.three_mul_entries_le_carriers,
        `Erdos64EG.Internal.p13Node147ArithmeticCheckCount_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-node148-live-hot-decision"
      title := "Node [148] live-hot entropy decision"
      summary := "On the accumulated node-[146] no state, the framework executes the corrected total-demand comparison. The two payloads add only the finite cap or the cold shortfall facts; the node-[145] ledger, threshold facts, and hot aggregate remain inherited rather than copied."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.p13Node148DecisionRefinement
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node148_hotDemand_le_allowance,
        `Erdos64EG.Internal.p13Node148_totalDemand_eq_hot_add_cold,
        `Erdos64EG.Internal.p13Node148_totalDemand_le_allowance_add_cold,
        `Erdos64EG.Internal.P13Node148To149,
        `Erdos64EG.Internal.P13Node148To150,
        `Erdos64EG.Internal.p13Node148To149Refinement,
        `Erdos64EG.Internal.p13Node148To150Refinement,
        `Erdos64EG.Internal.p13Node148LocalCheckCount_polynomial,
        `Erdos64EG.Internal.p13Node148WorkBudget_checks
      ]
    },
    {
      stageId := "proof-slice.p13-node149-density-cap"
      title := "Node [149] normalized P₁₃ density cap"
      summary := "The accumulated node-[148] yes state yields theta ≤ theta_win plus one explicit graph-order error tending to zero. Node [149] adds only its corrected density handoff; the framework retains every predecessor stage."
      kind := .theorem
      primaryDeclaration :=
        `Erdos64EG.Internal.VerifiedP13Node149DensityCap.theta_le_thetaWindow_add_oOne
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13Node149DensityCap,
        `Erdos64EG.Internal.p13Node149Refinement,
        `Erdos64EG.Internal.VerifiedP13Node149DensityCap.correctedThetaCap,
        `Erdos64EG.Internal.p13Node149ThetaWindow_eq_exact,
        `Erdos64EG.Internal.p13SequentialHotNormalizationError_real_upper,
        `Erdos64EG.Internal.p13SequentialHotNormalizationRealEnvelope_isLittleO,
        `Erdos64EG.Internal.p13Node149ThetaError_tendsto_zero,
        `Erdos64EG.Internal.VerifiedP13Node149DensityCap.correctedRemainderCap,
        `Erdos64EG.Internal.VerifiedP13Node149DensityCap.localCheckCount_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-node150-cold-mass"
      title := "Node [150] normalized cold-mass handoff"
      summary := "The accumulated node-[148] no state yields the paper's two printed cold-mass coefficients with a uniform vanishing normalization error. Node [150] adds only this cold-mass output; the framework retains the threshold, cap-failure, and weighted ledger inputs."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.p13Node150FiniteColdMass
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node150_manuscriptRoute8ColdMassCrossMultiplied,
        `Erdos64EG.Internal.p13Node150_manuscriptNegativeNetColdMassCrossMultiplied,
        `Erdos64EG.Internal.p13ManuscriptRoute8ColdMassCoefficient_printedBracket,
        `Erdos64EG.Internal.p13ManuscriptNegativeNetColdMassCoefficient_printedBracket,
        `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalizationError_real_upper,
        `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalizationRealEnvelope_isLittleO,
        `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero,
        `Erdos64EG.Internal.P13Node150FiniteColdMass,
        `Erdos64EG.Internal.p13Node150Refinement,
        `Erdos64EG.Internal.p13Node150LocalCheckCount_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-density-handoff"
      title := "Nodes [22]--[24] exact density branch"
      summary := "From the accumulated node-[21] ledger, node [22] makes the paper's exact scalar dichotomy, node [23] records the strict yes-edge overflow without an auxiliary assumption, and node [24] retains the complementary window cap plus its reusable high-entropy transformer."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode24
      evidenceDeclarations := [
        `Erdos64EG.Internal.node22DensityFamily,
        `Erdos64EG.Internal.Node22High,
        `Erdos64EG.Internal.Node22Low,
        `Erdos64EG.Internal.Node22Stage,
        `Erdos64EG.Internal.node22P13DensityDecision,
        `Erdos64EG.Internal.runInitialThroughNode22,
        `Erdos64EG.Internal.node22LocalChecks_eq_zero,
        `Erdos64EG.Internal.Node23Output,
        `Erdos64EG.Internal.node23StrictWindowOverflow,
        `Erdos64EG.Internal.Node23Stage,
        `Erdos64EG.Internal.node23P13WindowEntropyOverflow,
        `Erdos64EG.Internal.runInitialThroughNode23,
        `Erdos64EG.Internal.Node24HighEntropyJointBudget,
        `Erdos64EG.Internal.Node24HighEntropyCap,
        `Erdos64EG.Internal.node24HighEntropyCap_of_jointBudget,
        `Erdos64EG.Internal.Node24HighEntropyTransformer,
        `Erdos64EG.Internal.node24HighEntropyTransformer,
        `Erdos64EG.Internal.Node24Output,
        `Erdos64EG.Internal.Node24Stage,
        `Erdos64EG.Internal.node24StageEntailsHighEntropyTransformer,
        `Erdos64EG.Internal.node24P13DensityBounds,
        `Erdos64EG.Internal.node24LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageEntails
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
      summary := "From the exact node-[153] cold fork, the graph-owned degree, stub, deleted-edge-return, and first-event runners return exactly window surplus, a dyadic target hit, a corridor-high handoff, or a quiet ambient-finite structural germ."
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
      summary := "Every exact node-[21] packed window retains its classifier-produced thirteen-bit cold residual and computed node-[153] frontier; the four structural subledgers partition exactly p13 windows without being identified with the open 91-coordinate response system."
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
      summary := "Equality with the computed node-[153] quiet constructor permits one graph-owned support comparison at Qbase=4²·13²·2¹³, retaining exactly the literal short or strict long residual."
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
      summary := "Equality with node [153]'s computed short constructor fixes one bounded deleted-edge return; the graph root classifier selects its declared-order third incidence and returns exactly on-support or outside-boundary membership."
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
      summary := "Equality with node [153]'s computed outside constructor orients its one support-crossing incidence and packages the already cubic return root as a three-leaf star owning every root incidence."
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
      summary := "Equality with node [153]'s computed on-support constructor locates the selected endpoint once; an accepted local chord closes through CT1, while the surviving residual is the exact strictly shorter deleted-edge return."
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
      summary := "The exact node-[153] shorter-return and node-[153] outside-boundary computations rejoin into one branch-indexed return with an outside root incidence, cubic ownership, inherited Qbase bound, and strict-or-equal length evidence."
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
      summary := "One exact node-[153] return is scanned against the union of all ambient-cubic selected-window supports, yielding either full containment or the first membership transition with its exact boundary stub, outside endpoint, and induced-remainder component."
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
      summary := "The exact node-[153] first-transition stub is expanded by one computed deleted-edge return: a shared outside-component BFS supplies the first exit, an explicit first slot supplies a distinct second stub, the complete incident-stub list has a true cyclic successor, and declared-order BFS supplies a shortest component path."
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
      summary := "The exact node-[153] two-boundary schedule is projected to one genuine State (Fin 0): two literal boundary degrees, two literal window offsets, and the independently computed declared-order BFS-tree shortest-path length. The empty local response explicitly retains MissingD4D7 reconstruction."
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
      summary := "The exact node-[153] residual supplies the retained anchor state. The complete node-[153] incident schedule is scanned in its stored cyclic order, producing either two observed rows with the same coarse D1--D3 state or a proof that the schedule has length at most Qbase."
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
      summary := "The exact node-[153] result is consumed on the same context. A coarse repeat is promoted through CT10 on its retained pair; a bounded schedule scans only its actual rows and returns a reconstructed family or the first typed missing D4--D7 row, with that residual routed through CT10."
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
      summary := "The exact node-[153] execution is inspected once. The impossible complete-reconstruction constructor is eliminated from the actual anchor row; the remaining coarse and bounded branches retain their exact CT10 routes and typed missing D4--D7 witnesses."
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
      summary := "Equality with node [153]'s all-inside constructor prepares one stored unique ambient-cubic owner per return vertex; the impossible single-window branch is eliminated and the first owner change returns two exact cross-window tokens."
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
      summary := "The exact node-[153] first owner-change edge is projected without a new search into a typed pair of distinct opposite oriented contributions of the same literal edge; both retained token subtypes remain exactly cross-window."
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
      summary := "Equality with node [153]'s computed long constructor forces the first Qbase+1 literal support positions, their unique overflow index, and exact local prefix/after-prefix classifiers on the identical branch context."
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
      summary := "The exact node-[153] source maps its first nine literal prefix positions to corridor vertices, computes only degree modulo four and selected-packing membership, retains an actual collision in the eight-label alphabet, and executes CT10 on exactly the two collided occurrences."
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
      summary := "The exact node-[153] collision and promoted CT10 response-context obligation are retained. Only the two literal corridor degree rows are read, yielding equal full degrees or a nonzero degree gap with the same residue modulo four."
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
      summary := "The dyadic constructor of node [153] is converted, without a fresh witness, to the exact cold dyadic hit; the established one-check CT1 G1 run reaches C1 and contradicts target avoidance."
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
      title := "Node [35] functional rank circuit"
      summary := "On node [33]'s strict-loss marker, CT15 extracts the canonical proof-carrying pair circuit. Its candidate supplies the exact support-stratified determination certificate, while Core preserves the accumulated residual and sibling branches."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode35
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node35PairCircuit,
        `Erdos64EG.Internal.Node35CollisionSupportCertificate,
        `Erdos64EG.Internal.node35RankDropOnDeclaredCoordinates,
        `Erdos64EG.Internal.node35PairCircuit,
        `Erdos64EG.Internal.node35CollisionSupportCertificate,
        `Erdos64EG.Internal.Node35Output,
        `Erdos64EG.Internal.Node35Stage,
        `Erdos64EG.Internal.node35P13RankCircuit,
        `Erdos64EG.Internal.node35LocalChecks_eq_zero,
        `StructuralExhaustion.CT15.CertifiedDeterminationRank.Profile.pairCircuitOfRankDrop,
        `StructuralExhaustion.CT15.SupportStratifiedRank.Profile.certificate
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-context-validity"
      title := "Original-atom context audit"
      summary := "Node [36] consumes node [35]'s exact certificate and audits only the original atom interface. It returns either one concrete atom-context mismatch or universal equality at that atom; carrier-level target completeness is not transported across interfaces."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode36
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node36OriginalUniversal,
        `Erdos64EG.Internal.Node36OriginalDefect,
        `Erdos64EG.Internal.node36OriginalUniversalDecidable,
        `Erdos64EG.Internal.node36OriginalDefectOfNotUniversal,
        `Erdos64EG.Internal.node35ActiveCursorFamily,
        `Erdos64EG.Internal.Node36Stage,
        `Erdos64EG.Internal.node36P13OriginalContextAudit,
        `Erdos64EG.Internal.node36LocalChecks_eq_zero,
        `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.OriginalContextAudit,
        `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.auditOriginal
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-target-defect-terminal"
      title := "Target-defective quotient terminal"
      summary := "Node [37] marks only node [36]'s concrete original-interface mismatch leaf terminal; every sibling constructor remains framework-owned and unchanged."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode37
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node37TargetDefect,
        `Erdos64EG.Internal.Node37Stage,
        `Erdos64EG.Internal.node37P13TargetDefect,
        `Erdos64EG.Internal.node37LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.markActiveCursorYesContinuationNoTerminal
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-proper-representative-decision"
      title := "Original-versus-enlarged carrier decision"
      summary := "On node [36]'s universal edge, node [38] compares the certificate's final carrier with its original atom. The framework returns exactly the at-original or strict-enlargement constructor and retains the carrier-indexed representative without searching a support universe."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode38
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node38AtOriginal,
        `Erdos64EG.Internal.Node38Enlarged,
        `Erdos64EG.Internal.node38AtOriginalDecidable,
        `Erdos64EG.Internal.node38EnlargedOfNotAtOriginal,
        `Erdos64EG.Internal.Node38Stage,
        `Erdos64EG.Internal.node38P13ProperRepresentativeDecision,
        `Erdos64EG.Internal.node38LocalChecks_eq_zero,
        `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.Location,
        `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.location
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-proper-compression-terminal"
      title := "At-original CT3 compression terminal"
      summary := "Only node [38]'s literal at-original constructor transports the carrier representative to the original proper atom. The graph framework executes the stored CT3 compression and contradicts minimality."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode39
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node39Stage,
        `Erdos64EG.Internal.node39P13ProperAtomCompression,
        `Erdos64EG.Internal.node39LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeActiveCursorYesContinuationFinalYes,
        `StructuralExhaustion.Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-enlarged-support"
      title := "Strict enlarged-support payload"
      summary := "Node [40] focuses node [38]'s literal enlarged-support leaf. Its connectedness, strict inclusion, determination, and minimality remain in the single accumulated certificate rather than a copied application record."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode40
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node40Stage,
        `Erdos64EG.Internal.node40P13EnlargedConnectedSupport,
        `Erdos64EG.Internal.node40LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.focusActiveCursorYesContinuationFinalNo
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-carrier-scope"
      title := "Proper-or-whole carrier scope"
      summary := "Node [41] applies the framework focused-branch decision to the exact node-[40] carrier, yielding only the paper's proper or whole constructors."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode41
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node41Bypass,
        `Erdos64EG.Internal.Node41Active,
        `Erdos64EG.Internal.Node41Proper,
        `Erdos64EG.Internal.Node41Whole,
        `Erdos64EG.Internal.Node41Stage,
        `Erdos64EG.Internal.node41P13CarrierScopeDecision,
        `Erdos64EG.Internal.node41LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranch
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-proper-carrier-terminal"
      title := "Proper enlarged-carrier CT3 terminal"
      summary := "On node [41]'s proper constructor, node [42] consumes the representative's stored CT3 compression on that exact carrier and closes by minimality."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode42
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node42Stage,
        `Erdos64EG.Internal.node42ProperSupportImpossible,
        `Erdos64EG.Internal.node42P13ProperSupportSmearingClosure,
        `Erdos64EG.Internal.node42LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_originalEligible,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-whole-carrier"
      title := "Whole-carrier exact handoff"
      summary := "Node [43] continues node [41]'s literal whole leaf and transports that equality once to the determination certificate's equal carrier."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode43
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node43Output,
        `Erdos64EG.Internal.Node43Stage,
        `Erdos64EG.Internal.node43P13WholeGraphDelocalization,
        `Erdos64EG.Internal.node43LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-repair-identity"
      title := "One--three repair identity"
      summary := "Node [44] adds only the reusable one--three component identity to node [43]'s exact whole-carrier handoff."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode44
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node44Output,
        `Erdos64EG.Internal.Node44Stage,
        `Erdos64EG.Internal.node44P13RepairIdentity,
        `Erdos64EG.Internal.node44LocalChecks_eq_zero,
        `StructuralExhaustion.Core.OneThreeRepair.identity,
        `StructuralExhaustion.Graph.OneThreeRepair.Component.identity,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-closed-exact-barrier"
      title := "Whole-carrier exact-label barrier"
      summary := "Node [45] applies the graph-owned closed-carrier theorem to make the selected candidate's raw quotient code injective; no quotient or context family is enumerated."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode45
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node45Output,
        `Erdos64EG.Internal.Node45Stage,
        `Erdos64EG.Internal.node45P13GlobalProfileBarrier,
        `Erdos64EG.Internal.node45LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_whole,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-rank-drop-terminal"
      title := "Whole-carrier rank-drop contradiction"
      summary := "Node [46] applies node [45]'s injectivity to the distinct coordinate pair identified by node [35], closing the whole-carrier rank-drop edge."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode46
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node46Stage,
        `Erdos64EG.Internal.node46WholeRankDropImpossible,
        `Erdos64EG.Internal.node46P13RankDropClosure,
        `Erdos64EG.Internal.node46LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-curvature-full-rank-cross-panel"
      title := "Exact node-[47] full-rank handoff"
      summary := "Node [47] is definitionally the node-[34] stage. The framework retrieves that literal full-rank leaf unchanged after the independent rank-drop terminals."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode47
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node47Stage,
        `Erdos64EG.Internal.node47P13FullRankContinuation,
        `Erdos64EG.Internal.node47LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
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
        `Erdos64EG.Internal.surplusPairTransition_profile_id,
        `Erdos64EG.Internal.surplusPairTransition_context_preserved,
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
        `StructuralExhaustion.Routes.Accumulated.OutputLedger,
        `StructuralExhaustion.Routes.Accumulated.advanceCurrent,
        `Erdos64EG.Internal.surplusPortClassificationStage,
        `Erdos64EG.Internal.surplusPortClassificationLedger,
        `Erdos64EG.Internal.surplusPortClassificationTransition_profile_id,
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
        `StructuralExhaustion.Routes.Accumulated.OutputLedger,
        `StructuralExhaustion.Routes.Accumulated.advanceCurrent,
        `Erdos64EG.Internal.openPortPairStage,
        `Erdos64EG.Internal.openPortPairLedger,
        `Erdos64EG.Internal.openPortPairTransition_profile_id,
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
        `StructuralExhaustion.Graph.OpenPortResponse.transition_profile_id,
        `StructuralExhaustion.Graph.AdjacencyResponse.checks_linear
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
        `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedExecutionStage,
        `StructuralExhaustion.Graph.FiniteCertificateMarking.Profile.marked_or_residual_of_execution,
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
      summary := "A registered CT5-to-CT14 transition scans the actual cubic-closed-neighbour subtype, proves compatible-pair multiplicity at least two, and derives positive quarter deficit."
      kind := .tactic
      tacticId? := some "CT14"
      primaryDeclaration :=
        `Erdos64EG.Internal.exists_verifiedFanClosedMassPrefix
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.CT5ToCT14.transition_profile_id,
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
        `StructuralExhaustion.Routes.CT14ToCT14.transition_profile_id,
        `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card,
        `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card_le_twice_vertices,
        `StructuralExhaustion.Graph.HybridFanIncidence.other_injective,
        `StructuralExhaustion.Graph.HybridFanIncidence.multiplicity_partition,
        `StructuralExhaustion.Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack,
        `StructuralExhaustion.Graph.HybridFanIncidence.nonWindow_credit_pays_remaining,
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
        `Erdos64EG.Internal.hybridFanIncidenceStageAt
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
        `Erdos64EG.Internal.directFanWindowLedgerStage
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
        `Erdos64EG.Internal.twoWindowCycleLedgerStage
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
        `Erdos64EG.Internal.runFanLabelPackingCT9,
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
        `Erdos64EG.Internal.runMarkedFanLabelPackingCT9,
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
        `Erdos64EG.Internal.runCertificateClosedFanCT14,
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
        `Erdos64EG.Internal.verifiedPositiveDeficitFanEntryPrefix,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.degree_le_eight,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.two_le_closedCount,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.positiveDeficit,
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays,
        `Erdos64EG.Internal.hybridFanIncidenceStageAt,
        `Erdos64EG.Internal.PositiveDeficitFanFacts
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
        `Erdos64EG.Internal.activatedSurplusWork_le_cubic,
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
        `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedExecutionStage,
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
      summary := "All five exact node-[144] leaves are consumed. Mismatch and prefix leaves are retained verbatim; root and after-edge divergences expose literal distinct incidences and split only on the locally read separator degree."
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
      summary := "The exact node-[144] frontier is normalized without new checks: mismatch and prefix leaves are unchanged, cubic divergence leaves become literal four-vertex cubic-star data, and high leaves retain only degree at least four."
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
      summary := "The exact node-[153] markers are retained and assigned the fixed noduplicated D4,D5,D6,D7 obligation order. Coarse output has two ledgers and bounded output one; no clause truth is asserted."
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
      summary := "The exact node-[153] result and CT10 response-context obligation are retained. Adjacency of the two literal vertices is compared on the same nine prefix coordinates, producing the first mismatch or alignment on exactly those nine clauses."
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
      summary := "The exact node-[144] leaves are projected to literal cubic switch-boundary data or the identical high-center port row; mismatch and prefix leaves are unchanged."
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
      summary := "The exact node-[153] ledgers retain their dependent markers, focus D4 as the next obligation, and preserve the exact D5,D6,D7 tail without asserting truth."
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
      summary := "Every exact node-[144] leaf is retained and tagged with its next pending obligation. The tags are requests, not sparse-exit, CT3, Type B, or fixed-cap certificates."
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
      summary := "The exact node-[153] cursors emit one singleton D4 request per actual marker while retaining the dependent marker and literal D5,D6,D7 tail. No truth value is supplied."
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
      summary := "Node [144] retains the exact node-[144] payload and tag. Cubic leaves expose their three boundary incidences and high leaves their first four distinct declared ports; no requested semantic certificate is claimed."
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
      summary := "Each exact node-[153] request retains its dependent marker and D5--D7 tail and exposes exactly the missing graph-local predicate and provenance requirements. No evaluator or Boolean is accepted."
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
      summary := "The exact node-[144] certificate yields only pairwise boundary or endpoint inequalities and retains the pending semantic obligation unchanged. This is the manuscript-boundary residual interface."
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
      summary := "The exact node-[153] requests retain their markers and D5--D7 tails and are refined into the three graph-owned construction requirements. No predicate, evaluator, or Boolean is supplied."
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
      stageId := "proof-slice.p13-component-d4-evaluation"
      title := "Graph-owned D4 evaluation after node [153]"
      summary := "The exact node-[153] marker fixes one component path. The evaluator scans only its literal support wedges, computes the omegaTwo response for the two boundary-window roles, and retains D5--D7 unchanged."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathComponentD4.activeSupport,
        `StructuralExhaustion.Graph.InducedPathComponentD4.coordinates,
        `StructuralExhaustion.Graph.InducedPathComponentD4.response_true_iff,
        `StructuralExhaustion.Graph.InducedPathComponentD4.semantics,
        `StructuralExhaustion.Graph.InducedPathComponentD4.state_localResponse,
        `StructuralExhaustion.Graph.InducedPathComponentD4.visibleChecks_le_cubic,
        `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.run,
        `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.Evaluation.semantics_and_response_provenance,
        `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.Evaluation.tail_preserved,
        `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.visibleChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_exhaustive,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_localWork
      ]
    },
    {
      stageId := "proof-slice.p13-long-prefix-compatible-response-frontier"
      title := "Long-prefix compatible-response frontier"
      summary := "The exact five node-[153] leaves are retained. Each of the four mismatch leaves is now converted to a proved distinguishing adjacency response on one of the same 36 literal corridor positions; the aligned leaf stops at complete D4--D7 semantics and an exact-pair certified reduction."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.resolveP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_exhaustive,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_predecessor,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.requiredInputs_le_three,
        `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.visibleChecks_constant,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.responseContexts_card,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.ofFirstMismatch,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.ofSecondMismatch,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.ofThirdMismatch,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.ofFourthMismatch,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.exactType,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.resolve,
        `StructuralExhaustion.Graph.LongPrefixCT8Response.alignedReservedChecks_polynomial,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_degree_result,
        `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_ct10_responseContexts,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_requiredInputs,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_visibleChecks,
        `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_ambient_preserved,
        `Erdos64EG.Internal.resolveP13SameWindowLongPrefixCompatibleResponseFrontier,
        `Erdos64EG.Internal.resolveP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
        `Erdos64EG.Internal.p13SameWindowLongPrefixResponseVisibleChecks_eq,
        `Erdos64EG.Internal.p13SameWindowLongPrefixResponseVisibleChecks_polynomial
      ]
    },
    {
      stageId := "proof-slice.p13-forced-curvature-cost-split"
      title := "Forced curvature cost"
      summary := "Node [48] fixes the paper's exact curvature-cost constants and maps the literal node-[47] leaf. Its two finite accounting producers are missing; Core proves only the positive-scalar transport from those finite inequalities to the real-valued conclusions."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode48
      evidenceDeclarations := [
        `Erdos64EG.Internal.node48CurvatureEntropyCost,
        `Erdos64EG.Internal.node48WindowCurvatureDensity,
        `Erdos64EG.Internal.node48HighEntropyCurvatureDensity,
        `Erdos64EG.Internal.node48WindowForcedCost,
        `Erdos64EG.Internal.node48HighEntropyForcedCost,
        `Erdos64EG.Internal.node48CostError,
        `Erdos64EG.Internal.Node48Output,
        `Erdos64EG.Internal.Node48Stage,
        `Erdos64EG.Internal.node48P13ForcedCurvatureCost,
        `Erdos64EG.Internal.node48LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-finite-remainder-entropy"
      title := "Constrained remainder-graph entropy"
      summary := "Node [49] defines the original paper's constrained labelled-graph family G(R) on the fixed remainder carrier and its normalized entropy symbolically, without executing an enumeration of labelled graphs."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode49
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.State,
        `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.stateCount,
        `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.normalizedEntropy,
        `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.normalizedEntropy_eq,
        `Erdos64EG.Internal.node49RemainderGraphAdmissible,
        `Erdos64EG.Internal.node49RemainderGraphFamilyProfile,
        `Erdos64EG.Internal.node49RemainderGraphFamilyCount,
        `Erdos64EG.Internal.node49RemainderEntropy,
        `Erdos64EG.Internal.Node49Output,
        `Erdos64EG.Internal.Node49Output.entropyExact,
        `Erdos64EG.Internal.Node49Stage,
        `Erdos64EG.Internal.node49P13RemainderEntropy,
        `Erdos64EG.Internal.node49LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-entropy-scale-split"
      title := "Exact manuscript entropy dichotomy"
      summary := "Node [50] retains the exact node-[49] constrained-family entropy and applies the Core-owned ordered split to eta(R) and (1/10)log2 n, producing exactly the original yes and no edges with zero primitive inspections."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode50
      evidenceDeclarations := [
        `StructuralExhaustion.Core.OrderThresholdSplit.Profile.exhaustive,
        `Erdos64EG.Internal.Node50Bypass,
        `Erdos64EG.Internal.Node50Active,
        `Erdos64EG.Internal.node50EntropyThreshold,
        `Erdos64EG.Internal.node50EntropyProfile,
        `Erdos64EG.Internal.Node50High,
        `Erdos64EG.Internal.Node50Low,
        `Erdos64EG.Internal.Node50Stage,
        `Erdos64EG.Internal.node50P13EntropyDecision,
        `Erdos64EG.Internal.node50_exhaustive,
        `Erdos64EG.Internal.node50LocalChecks_eq_zero,
        `Erdos64EG.Internal.node50ThresholdWork_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorDecisionNoContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-high-remainder-bits"
      title := "High-entropy remainder bit contribution"
      summary := "Node [51] consumes only the manuscript high edge of node [50] over the constrained family G(R) and derives (|R|/10) log₂ n ≤ log₂ |G(R)| by symbolic arithmetic from node [49]'s exact entropy identity."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode51
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node51Output,
        `Erdos64EG.Internal.node51Output,
        `Erdos64EG.Internal.Node51Stage,
        `Erdos64EG.Internal.node51P13HighEntropyBranch,
        `Erdos64EG.Internal.node51LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
      ]
    },
    {
      stageId := "proof-slice.p13-window-remainder-accounting"
      title := "Node [52] joint window--remainder accounting"
      summary := "On node [51]'s literal high leaf, node [52] instantiates Core's symbolic base-plus-dependent-choice capacity theorem and powered joint-normalization profile. Remainder-preserving reglue fits the realized remainder family and every retained hot-window choice in one skeleton code; the powered inequality retains discarded hot scales and cold-window mass explicitly, without enumerating a product."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode52
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node52Output,
        `Erdos64EG.Internal.Node52JointCapacity,
        `Erdos64EG.Internal.Node52SkeletonCapacity,
        `Erdos64EG.Internal.Node52NormalizedJointCapacity,
        `Erdos64EG.Internal.Node52LogarithmicJointCapacity,
        `Erdos64EG.Internal.Node52JointBudget,
        `Erdos64EG.Internal.node52NormalizationProfile,
        `Erdos64EG.Internal.Node52Stage,
        `Erdos64EG.Internal.node52P13WindowRemainderAccounting,
        `Erdos64EG.Internal.node52LocalChecks_eq_zero,
        `Erdos64EG.Internal.node49_realizedRemainder_mul_hotChoices_le_skeletonCode,
        `StructuralExhaustion.Core.DependentOwnerGlueCapacity.BaseProfile.base_mul_localProduct_le_codeCard,
        `StructuralExhaustion.Core.PoweredJointNormalization.Profile.withError,
        `StructuralExhaustion.Core.PoweredJointNormalization.Profile.logb_withError,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
      ]
    },
    {
      stageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      title := "Accumulated remaining-budget decision"
      summary := "Node [53] consumes the exact low constructor retained beside node [52], compares the literal remaining labelled-skeleton bits with the inherited full-rank curvature cost, and retains both original outgoing edges. The high branch and every earlier bypass remain unchanged."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode53
      evidenceDeclarations := [
        `Erdos64EG.Internal.node53SkeletonBits,
        `Erdos64EG.Internal.node53WindowBits,
        `Erdos64EG.Internal.node53RemainderBits,
        `Erdos64EG.Internal.node53RemainingNoncurvatureBits,
        `Erdos64EG.Internal.node53ForcedCurvatureBits,
        `Erdos64EG.Internal.Node53Small,
        `Erdos64EG.Internal.Node53Large,
        `Erdos64EG.Internal.Node53Stage,
        `Erdos64EG.Internal.node53P13RemainingBudgetDecision,
        `Erdos64EG.Internal.node53LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
      ]
    },
    {
      stageId := "proof-slice.p13-entropy-cap-closure"
      title := "Two-edge entropy-cap terminal"
      summary := "Node [54] terminalizes node [52]'s high leaf by its proved joint budget. Its local strict-small contradiction is proved conditionally, while the node-[53] capacity producer remains missing."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode54
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node54HighTheta,
        `Erdos64EG.Internal.Node54HighOutput,
        `Erdos64EG.Internal.node54HighOutput,
        `Erdos64EG.Internal.Node54SmallCapacity,
        `Erdos64EG.Internal.node54SmallBudgetImpossible,
        `Erdos64EG.Internal.Node54Bypass,
        `Erdos64EG.Internal.Node54Active,
        `Erdos64EG.Internal.Node54Stage,
        `Erdos64EG.Internal.node54P13EntropyCapClosure,
        `Erdos64EG.Internal.node54LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      ]
    },
    {
      stageId := "proof-slice.p13-large-budget-residual"
      title := "Residual C marker"
      summary := "Node [55] is exactly node [53]'s complementary large-budget leaf after the two node-[54] terminals. It adds no inequality, density cap, or application-owned wrapper."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode55
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node55ResidualC,
        `Erdos64EG.Internal.Node55Stage,
        `Erdos64EG.Internal.node55P13LargeBudgetResidual,
        `Erdos64EG.Internal.node55LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
      ]
    },
    {
      stageId := "proof-slice.p13-net-deficiency-cap"
      title := "Residual C net-deficiency cap"
      summary := "Node [56] continues only node [55]'s literal Residual C leaf and proves the exact rational constant is below one quarter. The finite error-bearing net-deficiency producer remains missing on that leaf."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode56
      evidenceDeclarations := [
        `Erdos64EG.Internal.node56NetDeficiencyNumerator,
        `Erdos64EG.Internal.node56TauWindow,
        `Erdos64EG.Internal.node56NetError,
        `Erdos64EG.Internal.Node56Output,
        `Erdos64EG.Internal.node56TauWindow_lt_quarter,
        `Erdos64EG.Internal.Node56Stage,
        `Erdos64EG.Internal.node56P13NetDeficiencyCap,
        `Erdos64EG.Internal.node56LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
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
        `Erdos64EG.Internal.localTransition_not_enabled
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
      kind := .registeredTransition
      label := "registered CT1→CT12 transition"
      description := "The registered CT1 C1-to-CT12 transition consumes the exact induced-path realization, derives nonemptiness of the selected maximum family, runs CT12 on that family, and retains the preceding prefix unchanged."
      transitionProfileId? := some "CT1.terminal.c1->CT12"
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13PackingPrefix,
        `Erdos64EG.Internal.p13PackingPrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingPrefix,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingTransition_profile_id
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
      linkId := "proof-slice.p13-density-node25-remainder"
      sourceStageId := "proof-slice.p13-density-handoff"
      targetStageId := "proof-slice.p13-node25-large-remainder"
      kind := .frameworkComposition
      label := "node-[24] no leaf to Residual A"
      description := "The framework maps the exact node-[24] active leaf and appends only node [25]'s canonical remainder facts."
      evidenceDeclarations := [
        `Erdos64EG.Internal.node25P13LargeRemainder
      ]
    },
    {
      linkId := "proof-slice.p13-node25-node26"
      sourceStageId := "proof-slice.p13-node25-large-remainder"
      targetStageId := "proof-slice.p13-node26-remainder-continuation"
      kind := .frameworkComposition
      label := "Residual A crosses the panel"
      description := "Node [26] maps only the literal node-[25] cursor and names the same canonical remainder."
      evidenceDeclarations := [
        `Erdos64EG.Internal.node26P13RemainderContinuation
      ]
    },
    {
      linkId := "proof-slice.p13-node26-node27"
      sourceStageId := "proof-slice.p13-node26-remainder-continuation"
      targetStageId := "proof-slice.p13-node27-no-three-core"
      kind := .frameworkComposition
      label := "exclude an internal three-core"
      description := "Node [27] consumes the literal node-[26] remainder continuation and invokes only the existing remainder core lemmas."
      evidenceDeclarations := [
        `Erdos64EG.Internal.node27P13NoInternalThreeCore
      ]
    },
    {
      linkId := "proof-slice.p13-node27-positive-deficiency"
      sourceStageId := "proof-slice.p13-node27-no-three-core"
      targetStageId := "proof-slice.p13-positive-deficiency"
      kind := .frameworkComposition
      label := "exact remainder support"
      description := "Node [28] maps the literal node-[27] cursor and reads the graph-owned positive-deficiency profile on that same remainder."
      evidenceDeclarations := [
        `Erdos64EG.Internal.node28P13PositiveDeficiency
      ]
    },
    {
      linkId := "proof-slice.surplus-scale-multiscale-curvature"
      sourceStageId := "proof-slice.surplus-scale-split"
      targetStageId := "proof-slice.p13-multiscale-curvature"
      kind := .frameworkComposition
      label := "exact bounded constructor"
      description := "The node-[21] API is indexed by the literal bounded node-[19] constructor. Its optimized producer remains the sole open predecessor for the typed downstream chain."
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node21Stage
      ]
    },
    {
      linkId := "proof-slice.p13-multiscale-weighted-live-cold"
      sourceStageId := "proof-slice.p13-multiscale-curvature"
      targetStageId := "proof-slice.p13-weighted-live-cold"
      kind := .frameworkComposition
      label := "accumulate compatible hot or reject same-window cold"
      description := "Every exact node-[21] selected window is processed against the current recoverable hot aggregate. A compatible extension is retained; failure preserves the identical window and prior aggregate for the graph-owned cold corridor route."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13SequentialWeightedHotCount_add_coldCount,
        `Erdos64EG.Internal.P13WeightedColdBranchExcessStub.corridor
      ]
    },
    {
      linkId := "proof-slice.p13-density-type-a-57-63-local"
      sourceStageId := "proof-slice.p13-density-handoff"
      targetStageId := "proof-slice.type-a-nodes57-63-local-provenance"
      kind := .frameworkComposition
      label := "conditional original Part-V chain"
      description := "The eventual node-[56] inequality is converted to the exact finite strict-quarter payload, attached through the accumulated ledger, and passed to the original Part-V chain without discarding its error term."
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node57_eventually,
        `Erdos64EG.Internal.TypeANodes57To63Provenance.node57Refinement
      ]
    },
    {
      linkId := "proof-slice.type-a-63-to-86-88-local"
      sourceStageId := "proof-slice.type-a-nodes57-63-local-provenance"
      targetStageId := "proof-slice.type-a-nodes86-88-local-thresholds"
      kind := .frameworkComposition
      label := "conditional existing [63] to [86] continuation"
      description := "The threshold block accepts only the exact Type-A node-[63] support retained by the preceding conditional chain; it introduces no alternate diagram edge."
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANodes86To88Thresholds.node86
      ]
    },
    {
      linkId := "proof-slice.type-a-88-to-89-local"
      sourceStageId := "proof-slice.type-a-nodes86-88-local-thresholds"
      targetStageId := "proof-slice.type-a-node89-local-saturation"
      kind := .frameworkComposition
      label := "conditional existing [88] to [89] handoff"
      description := "The saturation decision is indexed by the literal node-[88] threshold residual and returns only the two original node-[89] outcomes."
      evidenceDeclarations := [
        `Erdos64EG.Internal.TypeANode89SaturationDecision.run
      ]
    },
    {
      linkId := "proof-slice.p13-weighted-live-cold-node153-exact-local"
      sourceStageId := "proof-slice.p13-weighted-live-cold"
      targetStageId := "proof-slice.p13-node153-produced-support-coverage"
      kind := .frameworkComposition
      label := "conditional cold-corridor continuation"
      description := "The exact local runner consumes a supplied node-[153] corridor survivor; the missing branch-total produced-support and ColdBoundedGerm producers remain explicit and are not bypassed by this workflow link."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.outside_all_produced_occurrences
      ]
    },
    {
      linkId := "proof-slice.p13-node153-coverage-exact-local"
      sourceStageId := "proof-slice.p13-node153-produced-support-coverage"
      targetStageId := "proof-slice.p13-node153-exact-continuation"
      kind := .frameworkComposition
      label := "conditional occurrence-complete F4 ledger"
      description := "The exact local continuation consumes the occurrence-preserving prior-support ledger through the typed LocalCorridorSurvivor connector; missing graph-owned global schedule producers remain upstream."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_completeProducedLedger,
        `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.runExactContinuation
      ]
    },
    {
      linkId := "proof-slice.p13-node153-node154-local-classifier"
      sourceStageId := "proof-slice.p13-node153-exact-continuation"
      targetStageId := "proof-slice.p13-node154-local-classifier"
      kind := .frameworkComposition
      label := "conditional existing F5-to-G1--G3 handoff"
      description := "This is the original node-[153] to node-[154] edge. The local classifier consumes a supplied bounded F5 germ; the graph-owned producer of that germ remains an explicit missing node-[153] obligation and is not fabricated by this link."
      evidenceDeclarations := [
        `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classify_exhaustive_with_trace
      ]
    },
    {
      linkId := "proof-slice.p13-weighted-live-cold-node146-threshold"
      sourceStageId := "proof-slice.p13-weighted-live-cold"
      targetStageId := "proof-slice.p13-node146-route8-threshold"
      kind := .frameworkComposition
      label := "decide the original route-8 density threshold"
      description := "The exact node-[145] packing-order ledger is retained on both outcomes while one cross-multiplied comparison selects the existing edge to node [147] or [148]."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node146AccumulatedRun
      ]
    },
    {
      linkId := "proof-slice.p13-node146-node147-arithmetic"
      sourceStageId := "proof-slice.p13-node146-route8-threshold"
      targetStageId := "proof-slice.p13-node147-private-carrier-arithmetic"
      kind := .frameworkComposition
      label := "yes: retain the strict route-8 margin"
      description := "The literal node-[146] yes payload supplies the denominator-safe tau bound and its equivalent positive collision coefficient; the existing route-8 carrier ledger is still required for terminal closure."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node147ArithmeticRefinement
      ]
    },
    {
      linkId := "proof-slice.p13-node146-node148-hot-decision"
      sourceStageId := "proof-slice.p13-node146-route8-threshold"
      targetStageId := "proof-slice.p13-node148-live-hot-decision"
      kind := .frameworkComposition
      label := "no: execute the live-hot comparison"
      description := "The exact node-[146] no payload is retained as an index while the already constructed final hot aggregate pays the hot demand and one corrected comparison selects the existing edge to node [149] or [150]."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node148DecisionRefinement
      ]
    },
    {
      linkId := "proof-slice.p13-node148-node149-density-cap"
      sourceStageId := "proof-slice.p13-node148-live-hot-decision"
      targetStageId := "proof-slice.p13-node149-density-cap"
      kind := .frameworkComposition
      label := "yes: normalize the finite density cap"
      description := "The exact predecessor-indexed node-[148] yes payload is normalized with the uniform graph-order error envelope to the original node-[149] density conclusion."
      evidenceDeclarations := [
        `Erdos64EG.Internal.VerifiedP13Node149DensityCap.theta_le_thetaWindow_add_oOne
      ]
    },
    {
      linkId := "proof-slice.p13-node148-node150-cold-mass"
      sourceStageId := "proof-slice.p13-node148-live-hot-decision"
      targetStageId := "proof-slice.p13-node150-cold-mass"
      kind := .frameworkComposition
      label := "no: retain the exact cold shortfall"
      description := "The exact node-[148] no payload is indexed unchanged while the failed hot comparison is converted into both manuscript cold-mass lower bounds. The separate surviving-spine state remains explicit."
      evidenceDeclarations := [
        `Erdos64EG.Internal.p13Node150FiniteColdMass
      ]
    },
    {
      linkId := "proof-slice.p13-multiscale-density-handoff"
      sourceStageId := "proof-slice.p13-multiscale-curvature"
      targetStageId := "proof-slice.p13-density-handoff"
      kind := .frameworkComposition
      label := "retain node [21] across the arithmetic split"
      description := "The framework consumes node [21], decides node [22], proves the local node-[23] closure conditionally, and retains node [24]'s complementary active leaf. The earlier missing producers are not counted as evidence."
      evidenceDeclarations := [
        `Erdos64EG.Internal.node22P13DensityDecision,
        `Erdos64EG.Internal.node23P13WindowEntropyOverflow,
        `Erdos64EG.Internal.node24P13DensityBounds
      ]
    },
    {
      linkId := "proof-slice.p13-multiscale-node21-partxi-route"
      sourceStageId := "proof-slice.p13-multiscale-curvature"
      targetStageId := "proof-slice.p13-node21-partxi-route"
      kind := .frameworkComposition
      label := "retain the exact node-[21] prefix"
      description := "The Part-XI route is indexed by the identical VerifiedP13MultiScaleCurvaturePrefix. It maps the graph-owned CT12 packing once and stores the computed actual-attachment fork and structural frontier for every selected window; it supplies auxiliary same-window geometry and no weighted density payment."
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
      description := "The exact node-[153] cold-fork value indexes the result. The framework first classifies the thirteen actual degrees, then selects the canonical cubic stub when appropriate and scans only its proof-carrying deleted-edge return."
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
      description := "The input retains equality with node [153]'s computed quiet constructor, including the exact fork, selected window, canonical stub, no-event proof, and structural germ. The framework performs only the support-length comparison."
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
      description := "The input records equality with node [153]'s computed short result. The baseline and quiet germ make the exact return root cubic; the graph runner selects only its third declared incidence and tests that endpoint against the retained bounded support."
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
      description := "The input records equality with node [153]'s exact outside result. The reusable graph layer retains that same support crossing, packages the already certified cubic root, and proves its three displayed leaves own all root incidences."
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
      description := "The input records equality with node [153]'s exact on-support result. The graph resolver scans only that supplied short support, constructs its literal chord, and otherwise returns the exact shorter deleted-edge return."
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
      description := "The branch input retains equality with node [153]'s actual runner and its exact strictly shorter return. The graph normalizer chooses that return and the old first step as its outside incidence."
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
      description := "The branch input retains equality with node [153]'s computed outside result. The graph normalizer keeps the original return, selected outside endpoint, and the same cubic root ownership."
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
      description := "The input stores equality with node [153]'s actual normalized result. Its return is viewed in the ambient graph, and its selected-window endpoint is proved to lie in the union of all ambient-cubic selected-window supports before the one-path transition scan."
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
      description := "The input retains equality with node [153]'s actual first-transition result and its exact stub, endpoint, and returned component. The graph layer uses that same computed outside BFS component for the exit scan, incident schedule, second stub, and shortest component path."
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
      description := "The consumer receives node [153]'s actual graph input and result. It independently runs the declared-order BFS tree on that computed component, then packages equality to that one computed shortest path as a rank; it does not order or scan a path family."
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
      label := "retained exact node-[153] state"
      description := "The ledger source contains the typed node-[153] residual together with equality to the actual node-[153] run. The anchor row is that retained state exactly; only non-anchor rows re-anchor node [153]'s complete local schedule."
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
      label := "consume the exact node-[153] split"
      description := "The source retains node [153]'s generic result and proves equality with the actual specialized P13 run. Both CT10 inputs preserve the identical branch context; no D4--D7 semantics are supplied by the caller."
      automationDeclarations := [
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseHandoffContract,
        `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingHandoffContract
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
      label := "consume the exact node-[153] execution"
      description := "The readiness source stores equality with the actual specialized node-[153] run. It eliminates only the constructor contradicted by the retained anchor stub and preserves every remaining local witness and CT10 route."
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
      description := "The input stores equality with node [153]'s actual all-inside result. The graph layer prepares the finite owner inventory and one stored unique owner for each vertex of that same return."
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
      description := "The source is node [153]'s complete first-cross-window package. The typed route only projects its two already computed endpoint tokens and records their opposite orientations on the same literal edge."
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
      description := "The input records equality with node [153]'s computed strict-long result. The generic route preserves the identical branch context and source while exposing the forced initial support segment."
      automationDeclarations := [
        `StructuralExhaustion.Routes.LongFiniteSupportHandoff.handoff
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
      description := "The source stores equality with node [153]'s actual run. The route inspects only the first nine literal corridor occurrences and passes exactly the collided pair to the CT10 refinement table."
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
      description := "The degree source contains the actual node-[153] result and its promoted CT10 response-context residual. The consumer reads exactly the two corridor vertices selected by that collision."
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
      linkId := "proof-slice.positive-deficiency-external-incidence"
      sourceStageId := "proof-slice.p13-positive-deficiency"
      targetStageId := "proof-slice.p13-external-incidence-supply"
      kind := .frameworkComposition
      label := "literal node-[28] remainder"
      description := "The node-[29] constructor consumes the dependent node-[28] value itself. The graph accounting kernel injects its deficiency into the unchanged remainder boundary and then into the already selected window-token schedule."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node29P13ExternalIncidenceSupply
      ]
    },
    {
      linkId := "proof-slice.external-incidence-wedge"
      sourceStageId := "proof-slice.p13-external-incidence-supply"
      targetStageId := "proof-slice.p13-wedge-lower"
      kind := .frameworkComposition
      label := "exact node-[29] deficiency supply"
      description := "The dependent node-[30] constructor receives the node-[29] value itself. The graph-owned degree-count theorem converts its exact deficiency ceiling into the componentwise and aggregate wedge floors."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node30P13WedgeLower
      ]
    },
    {
      linkId := "proof-slice.wedge-curvature-target-rank"
      sourceStageId := "proof-slice.p13-wedge-lower"
      targetStageId := "proof-slice.p13-curvature-target-rank"
      kind := .frameworkComposition
      label := "exact node-[30] wedge payload"
      description := "The dependent node-[31] constructor receives node [30] itself. The framework forms the literal wedge-coordinate family and its proof-selected maximum over support-certified quotient candidates."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node31P13CurvatureTargetRank
      ]
    },
    {
      linkId := "proof-slice.curvature-target-rank-decision"
      sourceStageId := "proof-slice.p13-curvature-target-rank"
      targetStageId := "proof-slice.p13-curvature-rank-decision"
      kind := .frameworkComposition
      label := "node-[31] declared rank object"
      description := "The node-[32] constructor receives node [31] itself and applies the framework's exact strict-loss-or-equality split to the same declared coordinate cardinality."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoYesClosedActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node32P13RankDropDecision
      ]
    },
    {
      linkId := "proof-slice.curvature-rank-drop-dependence"
      sourceStageId := "proof-slice.p13-curvature-rank-decision"
      targetStageId := "proof-slice.p13-curvature-dependence-open"
      kind := .frameworkComposition
      label := "node-[32] yes: strict rank loss"
      description := "Node [33] marks only the strict-rank-loss constructor with PUnit; it does not extract the pair circuit or copy node [32]'s proof."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node33P13RankReducingBranch
      ]
    },
    {
      linkId := "proof-slice.curvature-rank-decision-routing"
      sourceStageId := "proof-slice.p13-curvature-rank-decision"
      targetStageId := "proof-slice.p13-full-curvature-rank"
      kind := .frameworkComposition
      label := "node-[32] no: exact full rank"
      description := "Node [34] marks only the full-rank constructor with PUnit; the exact equality remains in node [32]'s framework decision."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionNo
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node34P13FullRankResidual
      ]
    },
    {
      linkId := "proof-slice.curvature-dependence-cross-panel"
      sourceStageId := "proof-slice.p13-curvature-dependence-open"
      targetStageId := "proof-slice.p13-curvature-rank"
      kind := .frameworkComposition
      label := "Branch D payload retained for node [35]"
      description := "The framework maps node [33]'s marker to CT15's pair circuit. The circuit-indexed support certificate remains a missing producer."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionYesContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node35P13RankCircuit
      ]
    },
    {
      linkId := "proof-slice.curvature-context-validity"
      sourceStageId := "proof-slice.p13-curvature-rank"
      targetStageId := "proof-slice.p13-curvature-context-validity"
      kind := .frameworkComposition
      label := "node-[35] original-interface audit"
      description := "The dependent node-[36] constructor receives node [35] itself and projects the framework-owned proof-level audit on the original atom's own context type."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node36P13OriginalContextAudit
      ]
    },
    {
      linkId := "proof-slice.curvature-target-defect-terminal"
      sourceStageId := "proof-slice.p13-curvature-context-validity"
      targetStageId := "proof-slice.p13-curvature-target-defect-terminal"
      kind := .frameworkComposition
      label := "node-[36] defect: concrete atom-context mismatch"
      description := "Node [37] receives node [36] and exactly one mismatch in the original atom's context type. It is retained as the manuscript's target-defect residual and is not closed from carrier universality."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.markActiveCursorYesContinuationNoTerminal
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node37P13TargetDefect
      ]
    },
    {
      linkId := "proof-slice.curvature-proper-representative-decision"
      sourceStageId := "proof-slice.p13-curvature-context-validity"
      targetStageId := "proof-slice.p13-curvature-proper-representative-decision"
      kind := .frameworkComposition
      label := "node-[36] universal: locate the carrier"
      description := "Node [38] receives node [36]'s universal atom-context edge and executes the framework's at-original versus strict-enlargement location split on the retained carrier."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuationYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node38P13ProperRepresentativeDecision
      ]
    },
    {
      linkId := "proof-slice.curvature-proper-compression-terminal"
      sourceStageId := "proof-slice.p13-curvature-proper-representative-decision"
      targetStageId := "proof-slice.p13-curvature-proper-compression-terminal"
      kind := .frameworkComposition
      label := "node-[38] at original: stored CT3 compression"
      description := "Node [39] consumes only the at-original constructor. The graph framework transports the carrier representative to the proper atom and executes its stored CT3 compression."
      automationDeclarations := [
        `StructuralExhaustion.Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node39P13ProperAtomCompression
      ]
    },
    {
      linkId := "proof-slice.curvature-enlarged-support"
      sourceStageId := "proof-slice.p13-curvature-proper-representative-decision"
      targetStageId := "proof-slice.p13-curvature-enlarged-support"
      kind := .frameworkComposition
      label := "node-[38] strict enlargement"
      description := "The framework focuses the literal enlarged constructor; every support property stays in the accumulated node-[35] certificate."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.focusActiveCursorYesContinuationFinalNo
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node40P13EnlargedConnectedSupport
      ]
    },
    {
      linkId := "proof-slice.curvature-carrier-scope"
      sourceStageId := "proof-slice.p13-curvature-enlarged-support"
      targetStageId := "proof-slice.p13-curvature-carrier-scope"
      kind := .frameworkComposition
      label := "node-[40] proper-or-whole scope"
      description := "Node [41] decides only the proper/whole tag already stored on the exact focused carrier."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranch
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node41P13CarrierScopeDecision
      ]
    },
    {
      linkId := "proof-slice.curvature-proper-carrier-terminal"
      sourceStageId := "proof-slice.p13-curvature-carrier-scope"
      targetStageId := "proof-slice.p13-curvature-proper-carrier-terminal"
      kind := .frameworkComposition
      label := "node-[41] proper: CT3 terminal"
      description := "The proper constructor routes directly to node [42], whose graph-owned representative executes the exact CT3 compression on that carrier."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node42P13ProperSupportSmearingClosure
      ]
    },
    {
      linkId := "proof-slice.curvature-whole-carrier"
      sourceStageId := "proof-slice.p13-curvature-carrier-scope"
      targetStageId := "proof-slice.p13-curvature-whole-carrier"
      kind := .frameworkComposition
      label := "node-[41] whole: exact handoff"
      description := "The whole constructor routes directly to node [43], where its equality is transported to the equal determination carrier; it does not pass through node [42]."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node43P13WholeGraphDelocalization
      ]
    },
    {
      linkId := "proof-slice.curvature-repair-identity"
      sourceStageId := "proof-slice.p13-curvature-whole-carrier"
      targetStageId := "proof-slice.p13-curvature-repair-identity"
      kind := .frameworkComposition
      label := "node-[43] one--three identity"
      description := "Node [44] retains node [43] exactly and adds only the reusable component identity."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node44P13RepairIdentity
      ]
    },
    {
      linkId := "proof-slice.curvature-closed-exact-barrier"
      sourceStageId := "proof-slice.p13-curvature-repair-identity"
      targetStageId := "proof-slice.p13-curvature-closed-exact-barrier"
      kind := .frameworkComposition
      label := "node-[44] exact labels"
      description := "Node [45] invokes the graph-owned admitted-quotient injectivity theorem on the exact whole candidate."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node45P13GlobalProfileBarrier
      ]
    },
    {
      linkId := "proof-slice.curvature-rank-drop-terminal"
      sourceStageId := "proof-slice.p13-curvature-closed-exact-barrier"
      targetStageId := "proof-slice.p13-curvature-rank-drop-terminal"
      kind := .frameworkComposition
      label := "node-[45] contradict retained collision"
      description := "Node [46] applies injectivity to node [35]'s literal quotient identification of distinct raw coordinates."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node46P13RankDropClosure
      ]
    },
    {
      linkId := "proof-slice.curvature-full-rank-cross-panel"
      sourceStageId := "proof-slice.p13-full-curvature-rank"
      targetStageId := "proof-slice.p13-curvature-full-rank-cross-panel"
      kind := .frameworkComposition
      label := "node-[34] no-rank-drop to node [47]"
      description := "The complementary full-rank constructor crosses the panel independently of Branch D. Node [47] is definitionally the same stage, retrieved without copying or rederiving any payload."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node47P13FullRankContinuation
      ]
    },
    {
      linkId := "proof-slice.global-rank-node48-product-split"
      sourceStageId := "proof-slice.p13-curvature-full-rank-cross-panel"
      targetStageId := "proof-slice.p13-forced-curvature-cost-split"
      kind := .frameworkComposition
      label := "exact node-[47] to node-[48] handoff"
      description := "Node [48] consumes the literal node-[47] full-rank value retrieved from the accumulated residual ledger. During the source migration, its two finite accounting conclusions are supplied by one certificate indexed by that exact leaf; Core derives the two cost-unit conclusions and transports every bypass and sibling unchanged."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node48P13ForcedCurvatureCost
      ]
    },
    {
      linkId := "proof-slice.node48-node49-finite-state-entropy"
      sourceStageId := "proof-slice.p13-forced-curvature-cost-split"
      targetStageId := "proof-slice.p13-finite-remainder-entropy"
      kind := .frameworkComposition
      label := "fixed remainder to constrained graph family"
      description := "The accumulated node-[48] stage fixes R and its current net-deficiency cap. The graph framework forms the symbolic finite subtype satisfying the four original constraints, while the active-cursor mapper retains every earlier ledger fact automatically."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node49P13RemainderEntropy
      ]
    },
    {
      linkId := "proof-slice.node49-node50-entropy-scale-split"
      sourceStageId := "proof-slice.p13-finite-remainder-entropy"
      targetStageId := "proof-slice.p13-entropy-scale-split"
      kind := .frameworkComposition
      label := "exact entropy to manuscript threshold"
      description := "Node [50] consumes the identical dependent node-[49] output from the accumulated ledger and uses the framework active-cursor decision so both original edges retain that exact value."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorDecisionNoContinuation
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node50P13EntropyDecision
      ]
    },
    {
      linkId := "proof-slice.node50-node51-high-remainder-bits"
      sourceStageId := "proof-slice.p13-entropy-scale-split"
      targetStageId := "proof-slice.p13-high-remainder-bits"
      kind := .frameworkComposition
      label := "manuscript high edge"
      description := "The framework continues only the exact high constructor of the accumulated node-[50] decision. Node [51] adds the symbolic bit inequality; the low constructor, bypass bundle, and every earlier ledger fact are retained unchanged."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node51P13HighEntropyBranch
      ]
    },
    {
      linkId := "proof-slice.node51-node52-window-remainder-accounting"
      sourceStageId := "proof-slice.p13-high-remainder-bits"
      targetStageId := "proof-slice.p13-window-remainder-accounting"
      kind := .frameworkComposition
      label := "same-leaf joint accounting"
      description := "The framework maps only node [51]'s exact high continuation and retrieves node [24]'s transformer from the single accumulated ledger. The same-context joint budget remains an explicitly conditional, leaf-indexed producer during migration."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuationDerived
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node52P13WindowRemainderAccounting
      ]
    },
    {
      linkId := "proof-slice.node50-node53-low-entropy-forced-cost-fit"
      sourceStageId := "proof-slice.p13-entropy-scale-split"
      targetStageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      kind := .frameworkComposition
      label := "actual strict-low constructor"
      description := "The exact node-[50] low constructor is still present beside node [52]'s high continuation. The framework decides node [53]'s printed remaining-budget comparison on that leaf and preserves every sibling."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node53P13RemainingBudgetDecision
      ]
    },
    {
      linkId := "proof-slice.node52-node54-high-entropy-terminal"
      sourceStageId := "proof-slice.p13-window-remainder-accounting"
      targetStageId := "proof-slice.p13-entropy-cap-closure"
      kind := .frameworkComposition
      label := "node-[52] high-theta terminal"
      description := "Node [54] consumes the exact node-[52] joint-budget output and rules out its strict reverse. The framework terminalizes only that high leaf."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node54HighOutput,
        `Erdos64EG.Internal.node54P13EntropyCapClosure
      ]
    },
    {
      linkId := "proof-slice.node53-node54-small-budget-terminal"
      sourceStageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      targetStageId := "proof-slice.p13-entropy-cap-closure"
      kind := .frameworkComposition
      label := "node-[53] small-budget terminal"
      description := "On node [53]'s yes edge, node [54] contradicts the strict-small inequality with the capacity certificate indexed by that identical low leaf. That capacity producer remains explicitly conditional during migration."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node54SmallBudgetImpossible,
        `Erdos64EG.Internal.node54P13EntropyCapClosure
      ]
    },
    {
      linkId := "proof-slice.node53-node55-large-budget-residual"
      sourceStageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      targetStageId := "proof-slice.p13-large-budget-residual"
      kind := .frameworkComposition
      label := "node-[53] large edge to Residual C"
      description := "After the two node-[54] terminal leaves are discharged, Core focuses node [53]'s exact complementary large-budget constructor. Node [55] is a zero-copy name for that surviving leaf and adds no density claim."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node54P13EntropyCapClosure,
        `Erdos64EG.Internal.node55P13LargeBudgetResidual
      ]
    },
    {
      linkId := "proof-slice.node55-node56-net-deficiency-cap"
      sourceStageId := "proof-slice.p13-large-budget-residual"
      targetStageId := "proof-slice.p13-net-deficiency-cap"
      kind := .frameworkComposition
      label := "Residual C finite net cap"
      description := "Node [56] continues only the literal node-[55] leaf and attaches its exact finite net-deficiency payload. The old cap is temporarily supplied by one certificate indexed by that leaf; all routing remains framework-owned."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node56P13NetDeficiencyCap
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
        `Erdos64EG.Internal.sparseSurplusLedgerStage
      ]
    },
    {
      linkId := "proof-slice.surplus-ct6-pairs"
      sourceStageId := "proof-slice.surplus-ct6"
      targetStageId := "proof-slice.surplus-pairs"
      kind := .registeredTransition
      label := "registered CT6→CT9 transition"
      description := "The framework transition consumes the actual CT6 active-ledger residual, preserves the complete accumulated ledger, and executes CT9 on exactly the graph-owned surplus-slot collection."
      transitionProfileId? := some "CT6.residual.activeLedger->CT9"
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedSurplusPairPrefix,
        `Erdos64EG.Internal.surplusPairLedger,
        `Erdos64EG.Internal.surplusPairTransition_profile_id,
        `Erdos64EG.Internal.surplusPairTransition_context_preserved
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
        `Erdos64EG.Internal.highCenterStructureLedgerStage,
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
        `StructuralExhaustion.Routes.Accumulated.advanceCurrent
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.Accumulated.OutputLedger,
        `Erdos64EG.Internal.surplusPortClassificationStage,
        `Erdos64EG.Internal.surplusPortClassificationLedger,
        `Erdos64EG.Internal.surplusPortClassificationTransition_profile_id,
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
        `StructuralExhaustion.Routes.Accumulated.advanceCurrent
      ]
      evidenceDeclarations := [
        `StructuralExhaustion.Routes.Accumulated.OutputLedger,
        `Erdos64EG.Internal.openPortPairStage,
        `Erdos64EG.Internal.openPortPairLedger,
        `Erdos64EG.Internal.openPortPairTransition_profile_id,
        `StructuralExhaustion.Graph.SurplusPortActivity.verifiedOpenPairStage
      ]
    },
    {
      linkId := "proof-slice.open-pairs-responses"
      sourceStageId := "proof-slice.open-port-pairs"
      targetStageId := "proof-slice.open-port-responses"
      kind := .registeredTransition
      label := "registered CT9→CT7 transition"
      description := "The framework transition exists only for the CT9 overload residual, preserves the complete accumulated ledger, and executes CT7 on its exact capacity-one pair of canonical port endpoints."
      transitionProfileId? := some "CT9.residual.overload->CT7"
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.OpenPortResponse.transition_profile_id,
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
        `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedExecutionStage
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
        `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedExecutionStage
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
      kind := .registeredTransition
      transitionProfileId? := some "CT5.residual.chargeLedger->CT14"
      label := "charge ledger to actual fan mass"
      description := "The framework extracts the actual CT5 charge residual, preserves the branch context, materializes CT14's empty trigger, and scans the semantic cubic-closed-neighbour subtype."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.FanClosedPortMass.verifiedStage,
        `Erdos64EG.Internal.fanClosedMassStage
      ]
    },
    {
      linkId := "proof-slice.hybrid-fan-incidence"
      sourceStageId := "proof-slice.fan-closed-mass"
      targetStageId := "proof-slice.hybrid-fan-incidence"
      kind := .registeredTransition
      transitionProfileId? := some "CT14.residual.capacity->CT14"
      label := "mass capacity to incidence refinement"
      description := "The framework extracts the actual CT14 capacity residual, preserves the branch context, and runs a second CT14 capability over the two-per-member incidence universe."
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
        `Erdos64EG.Internal.hybridFanIncidenceStageAt
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
        `Erdos64EG.Internal.directFanWindowLedgerStage
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
        `Erdos64EG.Internal.twoWindowCycleLedgerStage
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
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays
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
      description := "Node [144] receives node [144]'s actual collision trigger, unchanged attachment maps, and identical two rooted germs. It scans only the declared attachment coordinates and retains the exact five-way residual."
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
      label := "consume all five exact node-[144] leaves"
      description := "The consumer stores equality with node [144]'s actual classification and performs only the finite incidence/degree checks exposed by the selected leaf."
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
      label := "normalize the exact node-[144] switch"
      description := "The source stores equality with node [144]'s actual frontier; normalization only repackages its already proved incidences and degree branch."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckNormalizationSource_node178_exact]
    },
    {
      linkId := "proof-slice.component-d4d7-readiness-clause-schedule"
      sourceStageId := "proof-slice.p13-same-window-component-d4d7-readiness"
      targetStageId := "proof-slice.p13-component-d4d7-clause-schedule"
      kind := .frameworkComposition
      label := "schedule the exact missing-clause markers"
      description := "The source stores equality with node [153]'s actual result and retains each dependent marker while assigning only the fixed four-slot obligation order."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseSchedule_exact_node180]
    },
    {
      linkId := "proof-slice.long-prefix-degree-local-alignment"
      sourceStageId := "proof-slice.p13-same-window-long-prefix-degree-refinement"
      targetStageId := "proof-slice.p13-long-prefix-local-clause-alignment"
      kind := .frameworkComposition
      label := "compare the exact pair on nine literal coordinates"
      description := "The source stores equality with node [153]'s actual runner and reuses the exact first-nine occurrence map and retained CT10 obligation."
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
      label := "project the exact node-[144] leaves"
      description := "The source stores equality with node [144]'s actual normalized result and projects only its literal cubic support or declared high ports."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckLocalProjectionSource_node181_exact]
    },
    {
      linkId := "proof-slice.d4d7-schedule-cursor"
      sourceStageId := "proof-slice.p13-component-d4d7-clause-schedule"
      targetStageId := "proof-slice.p13-component-d4d7-clause-cursor"
      kind := .frameworkComposition
      label := "focus D4 in the exact node-[153] ledgers"
      description := "The cursor preserves every dependent marker and the exact D5--D7 tail; it supplies no clause truth."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.d4d7ClauseCursor_exact_node182]
    },
    {
      linkId := "proof-slice.local-alignment-extended-alignment"
      sourceStageId := "proof-slice.p13-long-prefix-local-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-extended-clause-alignment"
      kind := .frameworkComposition
      label := "extend only to literal positions 9--17"
      description := "The source stores equality with node [153]'s actual result and retains the nested degree and CT10 provenance."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixExtendedClauseSource.exact_node183]
    },
    {
      linkId := "proof-slice.local-projection-strong-frontier"
      sourceStageId := "proof-slice.semantic-bottleneck-local-projection"
      targetStageId := "proof-slice.semantic-bottleneck-strong-frontier"
      kind := .frameworkComposition
      label := "tag each exact leaf's pending obligation"
      description := "The exact node-[144] projection and payload pass unchanged; the tag records which theorem remains to be proved and supplies no certificate."
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
      description := "The exact node-[153] result passes through with all nested degree and CT10 provenance; only the third nine-coordinate block is newly inspected."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixThirdBlockClauseSource.exact_node186]
    },
    {
      linkId := "proof-slice.strong-frontier-first-clause"
      sourceStageId := "proof-slice.semantic-bottleneck-strong-frontier"
      targetStageId := "proof-slice.semantic-bottleneck-first-clause"
      kind := .frameworkComposition
      label := "expose the first literal separator clause"
      description := "The exact node-[144] payload and obligation tag are retained while only fixed-arity incidence data are exposed."
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
      description := "The exact node-[153] result and nested CT10 provenance pass through; only the fourth nine-coordinate block is inspected."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixFourthBlockClauseSource.exact_node189]
    },
    {
      linkId := "proof-slice.first-clause-pairwise-clause"
      sourceStageId := "proof-slice.semantic-bottleneck-first-clause"
      targetStageId := "proof-slice.semantic-bottleneck-pairwise-clause"
      kind := .frameworkComposition
      label := "derive only literal pairwise inequalities"
      description := "The exact node-[144] certificate and pending tag pass through; injectivity and adjacency yield only the fixed-arity pairwise clauses."
      evidenceDeclarations := [`Erdos64EG.Internal.semanticBottleneckPairwiseClauseSource_node190_exact]
    },
    {
      linkId := "proof-slice.d4-residual-construction-residual"
      sourceStageId := "proof-slice.p13-component-d4-evaluator-residual"
      targetStageId := "proof-slice.p13-component-d4-evaluator-construction-residual"
      kind := .frameworkComposition
      label := "name the graph-owned construction inputs"
      description := "Each exact node-[153] residual is retained and refined into component-local data, graph-owned predicate definition, and predicate derivation requirements."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191]
    },
    {
      linkId := "proof-slice.d4-construction-residual-evaluation"
      sourceStageId := "proof-slice.p13-component-d4-evaluator-construction-residual"
      targetStageId := "proof-slice.p13-component-d4-evaluation"
      kind := .frameworkComposition
      label := "construct and run the graph-owned D4 evaluator"
      description := "The graph-owned construction inputs at node [153] determine the literal D4 evaluator; its exhaustive run preserves the D5--D7 tail and records exact local-response provenance."
      evidenceDeclarations := [
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation,
        `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_exhaustive
      ]
    },
    {
      linkId := "proof-slice.fourth-block-compatible-response-frontier"
      sourceStageId := "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      targetStageId := "proof-slice.p13-long-prefix-compatible-response-frontier"
      kind := .frameworkComposition
      label := "freeze the exact response residual"
      description := "All five node-[153] leaves, degree provenance, and CT10 response-context tag are retained while the missing graph-owned semantic inputs are made explicit."
      evidenceDeclarations := [`Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192]
    }
  ]
}

private def p13Node39ProofStep : ExampleProofStepDescriptor := {
  stepId := "erdos.p13-curvature-proper-compression-terminal"
  stageId? := some "proof-slice.p13-curvature-proper-compression-terminal"
  title := "At-original CT3 compression contradicts minimality"
  plainExplanation := "Node [39] consumes only node [38]'s at-original constructor. The framework closes that exact leaf with the graph-owned stored-representative contradiction."
  formalStatement := "X=C\\Longrightarrow\\operatorname{Representative}(X)=\\operatorname{CT3Compression}(C)\\Longrightarrow\\bot"
  status := .implemented
  correspondence := .exact
  manuscriptRefs := [
    { label := "cor:uncompressible", title := "Proper atom compression terminal", nodeIds := [39] }
  ]
  declarationGroups := [{
    groupId := "p13-node39-proper-compression-terminal"
    title := "Exact support transport and stored CT3 closure"
    role := .semanticTheorem
    explanation := "Core closes only the final yes leaf; the application supplies the graph theorem and no routing record."
    declarations := [
      `Erdos64EG.Internal.runInitialThroughNode39,
      `Erdos64EG.Internal.Node39Stage,
      `Erdos64EG.Internal.node39P13ProperAtomCompression,
      `Erdos64EG.Internal.node39LocalChecks_eq_zero,
      `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeActiveCursorYesContinuationFinalYes,
      `StructuralExhaustion.Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
    ]
  }]
  scopeNotes := "Node [39] closes only the at-original edge. Node [38]'s strict-enlargement edge proceeds independently to node [40]."
  workBound := "Zero searches: one dependent equality transport and one stored CT3 compression theorem. No candidate, coordinate, quotient, context, support, path, subgraph, graph, or state family is enumerated."
}

private def p13Node38ProofStep : ExampleProofStepDescriptor := {
  stepId := "erdos.p13-curvature-proper-representative-decision"
  stageId? := some "proof-slice.p13-curvature-proper-representative-decision"
  title := "Original-versus-enlarged carrier decision"
  plainExplanation := "After node [36] proves universal response at the original atom, node [38] compares the selected certificate's final carrier with that atom. It returns exactly equality or strict support growth, while keeping the representative indexed by the final carrier."
  formalStatement := "X=C\\quad\\lor\\quad C\\subsetneq X"
  status := .implemented
  correspondence := .exact
  manuscriptRefs := [
    { label := "lem:curvature-dependence-routing", title := "Proper representative decision", nodeIds := [38] }
  ]
  declarationGroups := [{
    groupId := "p13-node38-proper-representative"
    title := "Exact universal predecessor and support-location split"
    role := .semanticTheorem
    explanation := "The framework decides only the live universal leaf and preserves the target-defect terminal and every outer branch."
    declarations := [
      `Erdos64EG.Internal.runInitialThroughNode38,
      `Erdos64EG.Internal.Node38AtOriginal,
      `Erdos64EG.Internal.Node38Enlarged,
      `Erdos64EG.Internal.node38AtOriginalDecidable,
      `Erdos64EG.Internal.node38EnlargedOfNotAtOriginal,
      `Erdos64EG.Internal.Node38Stage,
      `Erdos64EG.Internal.node38P13ProperRepresentativeDecision,
      `Erdos64EG.Internal.node38LocalChecks_eq_zero,
      `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.Location,
      `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.location,
      `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuationYes
    ]
  }]
  scopeNotes := "Node [38] performs only the original support-location diamond. Node [39] consumes equality; node [40] consumes strict enlargement."
  workBound := "Zero executable scans. The comparison is proof-level on two stored support values; no support, candidate, coordinate, quotient, context, path, subgraph, graph, or state family is enumerated."
}

private def p13Node37ProofStep : ExampleProofStepDescriptor := {
  stepId := "erdos.p13-curvature-target-defect-terminal"
  stageId? := some "proof-slice.p13-curvature-target-defect-terminal"
  title := "Target-defective original-interface residual"
  plainExplanation := "If node [36] finds a mismatch, node [37] marks that exact original-interface witness terminal. It neither closes nor inspects the universal sibling."
  formalStatement := "\\exists K_C,\\ \\rho_C(a,K_C)\\ne\\rho_C(b,K_C)"
  status := .implemented
  correspondence := .exact
  manuscriptRefs := [
    { label := "lem:curvature-dependence-routing", title := "Target-defective quotient", nodeIds := [37] }
  ]
  declarationGroups := [{
    groupId := "p13-node37-target-defect-terminal"
    title := "Concrete original-interface defect witness"
    role := .semanticTheorem
    explanation := "The witness is already node [36]'s no predicate; Core marks only that leaf terminal without an application-owned payload."
    declarations := [
      `Erdos64EG.Internal.runInitialThroughNode37,
      `Erdos64EG.Internal.Node37TargetDefect,
      `Erdos64EG.Internal.Node37Stage,
      `Erdos64EG.Internal.node37P13TargetDefect,
      `Erdos64EG.Internal.node37LocalChecks_eq_zero,
      `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.markActiveCursorYesContinuationNoTerminal
    ]
  }]
  scopeNotes := "Node [37] fulfills only the target-defect output responsibility of the original edge. It neither consumes node [36]'s universal constructor nor asserts a contradiction from a differently indexed carrier interface."
  workBound := "Zero new executable checks after the proof-level audit. No context, coordinate, quotient, support, path, subgraph, graph, or state family is enumerated."
}

set_option maxRecDepth 100000 in
private def erdosManuscript : ExampleManuscriptDescriptor := {
  title := "Erdős--Gyárfás Problem 64 proof"
  path := "proofs/erdos_64_eg/erdos_64_proof.tex"
  /- Whole-node status against the claims in `original_erdos_64_proof.tex`.
  A node is listed only when Lean proves the original cell's complete claim,
  not merely a later repaired prefix or replacement.  Implemented proof-step
  references absent from this list are displayed yellow as partial coverage. -/
  formalizedNodeIds := [
    1, 2, 3,
    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20
  ]
  nodeObligations :=
    ExampleNodeObligationDescriptor.provedForStep 7 "erdos.mersenne-target" [
      ("N7-PRED", "Consume the literal node-[6] certificate decision."),
      ("N7-CYCLE", "Interpret the stored C1 certificate as the official power-of-two-cycle target."),
      ("N7-CLOSE", "Contradict that target with the inherited minimal-counterexample avoidance theorem."),
      ("N7-SURVIVOR", "Retain the literal CT1 avoiding run as the sole live node-[6] successor.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 8 "erdos.no-proper-core" [
      ("N8-PRED", "Consume only node-[7]'s exact surviving CT1 avoiding successor."),
      ("N8-CORE", "Exclude every proper subgraph of minimum degree at least three by minimality."),
      ("N8-CT2", "Retain the canonical certified CT2 deletion terminal and trace for each supplied proper core."),
      ("N8-WORK", "Use one local certificate check and enumerate no subgraph family.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 9 "erdos.deletion-criticality" [
      ("N9-PRED", "Consume the literal node-[8] stage."),
      ("N9-DELETE", "Apply the graph-owned deletion-criticality theorem on that selected graph."),
      ("N9-DEG3", "Prove every edge has a degree-three endpoint."),
      ("N9-LEDGER", "Append the endpoint theorem once to the accumulated ledger.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 10 "erdos.deletion-criticality" [
      ("N10-PRED", "Consume the literal node-[9] stage."),
      ("N10-QUERY", "Use node [9]'s stored degree-three endpoint theorem without rederivation."),
      ("N10-INDEP", "Prove vertices of degree at least four are independent."),
      ("N10-LEDGER", "Append only the independence theorem.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 11 "erdos.boundaried-replacement" [
      ("N11-PRED", "Consume the literal node-[10] stage."),
      ("N11-ATOMS", "Define exactly the proper boundaried atoms of the selected graph."),
      ("N11-PROFILE", "Attach each atom's uncapped boundary-degree profile."),
      ("N11-LEDGER", "Append only the atom/profile family.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 12 "erdos.boundaried-replacement" [
      ("N12-PRED", "Consume the literal node-[11] atom/profile stage."),
      ("N12-SCOPE", "Retain the identical selected graph and proper-atom scope."),
      ("N12-UNIVERSAL", "Prove every target-complete identification is context-universal."),
      ("N12-LEDGER", "Append only the context-universality implication.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 13 "erdos.boundaried-replacement" [
      ("N13-PRED", "Consume the literal node-[12] stage."),
      ("N13-REPLACE", "Exclude every exact one-way obstruction-preserving smaller replacement."),
      ("N13-CT3", "Retain the graph-owned certified CT3 terminal, trace, totality, and work theorem."),
      ("N13-LEDGER", "Append only the replacement contradiction.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 14 "erdos.boundaried-replacement" [
      ("N14-PRED", "Consume the literal node-[13] replacement stage."),
      ("N14-UNCOMP", "Convert a target-complete compression to node [13]'s replacement data and close it."),
      ("N14-DEFECT-NOT-COMPLETE", "Use node [12] to show a context-defective identification is not target-complete."),
      ("N14-DEFECT-WITNESS", "Retain the distinguishing-context target-defect certificate."),
      ("N14-SCOPE", "Quantify both clauses only over proper atoms.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 15 "erdos.induced-p13" [
      ("N15-PRED", "Consume only the literal node-[14] hereditary-uncompressibility stage."),
      ("N15-DECIDE", "Make the exhaustive framework decision between P13-free and not P13-free on the identical selected graph."),
      ("N15-BRANCHES", "Retain both exact decision constructors without manufacturing a path witness or sibling assumption."),
      ("N15-WORK", "Perform zero graph, path, context, or support scans at this proof-level decision.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 16 "erdos.induced-p13" [
      ("N16-PRED", "Consume the literal node-[15] decision stage."),
      ("N16-HSS", "Apply the isolated HSS theorem only to node [15]'s P13-free yes constructor."),
      ("N16-TARGET", "Interpret the HSS cycle as the official target on the identical selected graph."),
      ("N16-CLOSE", "Contradict that target with the inherited target-avoidance theorem."),
      ("N16-SURVIVOR", "Retain only node [15]'s literal not-P13-free constructor for node [17].")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 17 "erdos.p13-packing" [
      ("N17-PRED", "Consume only node-[16]'s exact surviving not-P13-free stage."),
      ("N17-PACK", "Select the framework's deterministic vertex-disjoint induced-P13 list on that graph."),
      ("N17-DISJOINT", "Certify nodup support and pairwise vertex disjointness for the selected list."),
      ("N17-MAXIMAL", "Certify saturation: every induced P13 meets a selected window; no maximum-cardinality claim is made."),
      ("N17-NONEMPTY", "Derive nonemptiness from the retained not-P13-free constructor."),
      ("N17-CT12", "Retain the exhausted CT12 terminal, typed trace, totality, and selected-list work certificate."),
      ("N17-CURSORS", "Expose the identical live context, selected windows, and packing number through framework-aligned accessors.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 18 "erdos.p13-labels" [
      ("N18-PRED", "Consume the literal node-[17] maximal-packing stage and its public live-context cursor."),
      ("N18-LABELS", "Certify exactly 399 legal P13 labels and the seven exact size fibres."),
      ("N18-REL", "Identify every executable C_s entry with the manuscript compatibility relation."),
      ("N18-CURV", "Identify Omega_2 with the exact two-compatible-one-incompatible curvature condition."),
      ("N18-ACTUAL", "Prove every actual nonempty outside attachment label on the retained graph is legal."),
      ("N18-CT10", "Retain the exhaustive CT10 stage, exact trace, totality, and symbolic polynomial work evidence.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 19 "erdos.surplus-scale-split" [
      ("N19-PRED", "Consume the literal node-[18] label-algebra stage and identical selected graph."),
      ("N19-VALUE", "Read the actual total surplus, graph order, and fixed homogeneous-cap coefficient without reconstructing an old prefix."),
      ("N19-DECIDE", "Produce the exact exhaustive strict-high or at-most squared-surplus constructors."),
      ("N19-WORK", "Use the framework's zero-scan symbolic comparison and work certificate.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 20 "erdos.surplus-scale-split" [
      ("N20-PRED", "Identify node [20] with node [19]'s literal strict-high constructor."),
      ("N20-STRICT", "Retain the exact strict squared-surplus proposition definitionally, without copying it into an application residual."),
      ("N20-SCOPE", "Add no surplus-pair mathematics before the existing node-[125] expansion."),
      ("N20-WORK", "Add zero checks beyond node [19]'s symbolic comparison.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 21 "erdos.p13-multiscale-curvature" [
      ("N21-PRED", "Consume only the literal node-[19] bounded/no constructor and no other branch."),
      ("N21-BUDGET", "Attach the inherited bounded-surplus square certificate without recomputing or strengthening it."),
      ("N21-PAIRS", "Classify the 196 ordered local length pairs and retain exactly the 91 positive pairs with sum at most fourteen."),
      ("N21-SEMANTICS", "Identify all fifteen packed 399-row relations with the manuscript's sparse P13 compatibility semantics on the complete local label carrier."),
      ("N21-SAFE", "Prove every stored safe count equals the reusable finite-relation barrier safe count."),
      ("N21-FLAT", "Prove every stored composition-flat count equals the reusable finite-relation barrier flat count."),
      ("N21-ONEONE", "Kernel-certify the exact 543958, 432672, and 111286 scale-(1,1) values."),
      ("N21-RATE", "Kernel-certify the exact 118-bit product inequality on the 91 accepted pairs."),
      ("N21-CT10", "Package the sole-HSS-clean semantic and count certificates in the single framework CT10 table interface."),
      ("N21-WORK", "Retain the symbolic polynomial work bound without unfolding an ambient graph, state, context, or Boolean universe.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 22 "erdos.p13-density-handoff" [
      ("N22-PRED", "Consume the exact node-[21] output from the single accumulated framework ledger on node [19]'s bounded edge."),
      ("N22-COMPARE", "Compare the exact fixed-point window load with the near-cubic skeleton load."),
      ("N22-YES", "Retain the strict-high constructor for node [23]."),
      ("N22-NO", "Retain the complementary at-most constructor for node [24]."),
      ("N22-WORK", "Use the framework's proof-level ordered split with zero local scans.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 23 "erdos.p13-density-handoff" [
      ("N23-PROV", "Consume exactly node [22]'s strict-high constructor."),
      ("N23-OVERFLOW", "Expose the same strict cross-multiplied window overflow and no successor conclusion."),
      ("N23-OUTPUT", "Attach the strict overflow to node [22]'s literal yes constructor without assuming branch emptiness."),
      ("N23-WORK", "Perform no graph, context, Boolean-state, or ambient-universe scan.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 24 "erdos.p13-density-handoff" [
      ("N24-PROV", "Retain the exact node-[22] no-edge and identical node-[21] packing."),
      ("N24-FINITE-CAP", "Retain the exact window-density inequality from node [22]'s at-most constructor."),
      ("N24-SUPPORT", "Use the graph-owned disjoint-packing support bound 13p13 <= n."),
      ("N24-TRANSFORM", "Prove the symbolic implication from a later joint window-remainder budget to the sharper high-entropy cap."),
      ("N24-LEDGER", "Register Node24HighEntropyTransformer once through StageEntails for later ledger retrieval."),
      ("N24-CONTINUE", "Continue only the surviving no leaf through the framework active cursor."),
      ("N24-WORK", "Use zero local scans and only symbolic natural-number arithmetic.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 25 "erdos.p13-node25-large-remainder" [
      ("N25-PROV", "Consume the literal node-[24] active output on the identical packing."),
      ("N25-PARTITION", "Retain the exact CT12 packing/remainder partition."),
      ("N25-FREE", "Retain remainder and componentwise induced-P13 freeness."),
      ("N25-LARGE", "Derive the exact scaled large-remainder inequality from node [24]'s window cap."),
      ("N25-WORK", "Perform no new graph scan; reuse the selected packing and zero-check connector.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 26 "erdos.p13-node26-remainder-continuation" [
      ("N26-PROV", "Consume the literal node-[25] active output."),
      ("N26-HANDOFF", "Identify the Part-II Residual A name with the same canonical packing complement."),
      ("N26-WORK", "Use the framework mapper with zero local checks and no copied predecessor fields.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 27 "erdos.p13-node27-no-three-core" [
      ("N27-PROV", "Consume the exact node-[26] residual on the identical graph, packing, and remainder."),
      ("N27-INDUCED-CORE", "Prove that the exact remainder has no induced internal support of minimum degree at least three."),
      ("N27-SUBGRAPH-CORE", "Prove the manuscript's stronger formulation: no finite internal subgraph of the exact remainder has minimum degree at least three."),
      ("N27-WORK", "Use the existing graph lemmas with zero new graph, component, subgraph, or support scans.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 28 "erdos.p13-positive-deficiency" [
      ("N28-PROV", "Consume the exact node-[27] output on the identical graph, packing, and remainder."),
      ("N28-DEGREE", "Define d_R(v) as the induced degree of v in the literal remainder."),
      ("N28-FORMULA", "Define def+(R) as the sum over v in R of max(0,3-d_R(v)), represented by natural subtraction."),
      ("N28-WORK", "Reuse the graph profile definition with zero new ambient-support or subgraph enumeration.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 29 "erdos.p13-external-incidence-supply" [
      ("N29-PROV", "Consume the exact dependent node-[28] output on the identical graph, packing, and remainder."),
      ("N29-BOUNDARY", "Charge every positive-deficiency unit to a literal incidence leaving the remainder, proving def+(R) <= e(R,W)."),
      ("N29-TOKENS", "Embed every R-W incidence in the selected-window external-token schedule."),
      ("N29-EXACT", "Prove the exact selected-window identity tokenCount = 15 p13 + sigma_W."),
      ("N29-SUPPLY", "Derive the window-surplus, total-surplus, and signed surplus-adjusted supply inequalities."),
      ("N29-SPINE", "Use the inherited bounded-surplus square certificate to bound the finite incidence error squared."),
      ("N29-WORK", "Use at most 13 n^2 local incidence checks on the selected windows, without enumerating paths, packings, supports, subgraphs, graphs, states, or contexts.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 30 "erdos.p13-wedge-lower" [
      ("N30-PROV", "Consume the exact dependent node-[29] output on the identical graph, packing, and remainder."),
      ("N30-COMPONENT", "For every remainder component C, prove W2(C) >= 3|V(C)| - 2 def+(C) by the local degree count."),
      ("N30-AGGREGATE", "Apply the same exact degree-count theorem to the literal remainder and obtain W2(R) >= 3|R| - 2 def+(R)."),
      ("N30-WINDOW", "Combine node [29]'s finite deficiency supply with the aggregate wedge floor, retaining the selected-window and total-surplus error exactly."),
      ("N30-WINDOW-RATE", "Transport the window-only deficiency coefficient to omega_win = 3 - 2 tau_win and verify the manuscript's printed decimal lower approximation."),
      ("N30-SPINE", "Use node [29]'s exact finite squared-error producer without copying the earlier certificate."),
      ("N30-WORK", "Use local degree-count and arithmetic transport only; enumerate no component, support, quotient, context, or ambient universe.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 31 "erdos.p13-curvature-target-rank" [
      ("N31-PROV", "Consume the exact dependent node-[30] output on the identical graph, packing, remainder, and wedge profile."),
      ("N31-COORDINATES", "Define the raw curvature tests as exactly one remainder center and one canonical unordered pair of distinct internal neighbours."),
      ("N31-COUNT", "Prove that the declared coordinate schedule has cardinality exactly W2(R), and at most n^3."),
      ("N31-RESPONSE", "Evaluate each coordinate by the exact target response of its literal three-vertex supported piece under every outside context."),
      ("N31-CARRIER-UNIVERSE", "Define the proof-carrying connected boundaried carrier universe on which every admitted curvature quotient is indexed."),
      ("N31-RANK", "Use FunctionalAdmissibleRank's attained carrier-indexed maximum and prove its W2(R) upper bound."),
      ("N31-WORK", "Define the maximum propositionally without evaluating a powerset, quotient, context, support, path, subgraph, or graph universe.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 32 "erdos.p13-curvature-rank-decision" [
      ("N32-PROV", "Consume the exact dependent node-[31] output on the identical graph, remainder, wedge family, response profile, and target-rank object."),
      ("N32-UPPER", "Use node [31]'s bound rOmega(R) <= W2(R) on the literal raw-coordinate schedule."),
      ("N32-YES", "Represent the original yes edge by strict loss below W2(R)-epsilon, with the current exact finite epsilon equal to zero."),
      ("N32-NO", "Represent the original no edge by reaching the same W2(R)-epsilon threshold."),
      ("N32-EXHAUSTIVE", "Use the framework decision to produce exactly those two constructors and no third edge."),
      ("N32-WORK", "Perform zero executable scans after node [31], without evaluating coordinate subfamilies, quotients, contexts, supports, paths, subgraphs, graphs, or state universes.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 33 "erdos.p13-curvature-dependence-open" [
      ("N33-PROV", "Consume only node [32]'s literal strict-rank-loss constructor."),
      ("N33-MARK", "Attach the PUnit branch marker required by the cross-panel edge to node [35]."),
      ("N33-SCOPE", "Leave pair-circuit and support-certificate construction to node [35]."),
      ("N33-WORK", "Use the framework yes-continuation with zero local checks.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 34 "erdos.p13-full-curvature-rank" [
      ("N34-PROV", "Consume only node [32]'s literal full-rank constructor."),
      ("N34-MARK", "Attach the PUnit branch marker required by the separate edge to node [47]."),
      ("N34-SCOPE", "Keep the exact rank proposition in node [32]'s branch proof instead of copying it into a new payload."),
      ("N34-WORK", "Use the framework no-continuation with zero local checks.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 35 "erdos.remainder-curvature-rank" [
      ("N35-PROV", "Consume node [33]'s literal rank-drop marker and node [32]'s retained strict-loss proof."),
      ("N35-PAIR", "Retain the identical distinct raw-coordinate pair and its exact quotient-code collision."),
      ("N35-BASIS", "Retain the singleton determining basis and prove that the determined coordinate is not in it."),
      ("N35-DETERMINATION", "Retain the support-stratified determination relation already certified by the selected CT15 candidate."),
      ("N35-SUPPORT", "Project the collision-to-support certificate directly from the selected proof-carrying CT15 candidate."),
      ("N35-INDEX", "Use CT15's exactness fields to identify the certificate's quotient code, basis, determined coordinate, and carrier with the extracted circuit."),
      ("N35-WORK", "Proof-select the current certificate and transport its value with zero executable scans.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 36 "erdos.p13-curvature-context-validity" [
      ("N36-PROV", "Consume node [35]'s exact certificate on the identical original atom and final carrier."),
      ("N36-AUDIT", "Make the exhaustive proof-level decision between one original-atom context mismatch and universal equality over that atom's own context type."),
      ("N36-INTERFACE", "Keep atom contexts distinct from carrier contexts; do not infer atom universality from carrier target completeness."),
      ("N36-WORK", "Use the zero-check framework audit and enumerate no contexts or supports.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 37 "erdos.p13-curvature-target-defect-terminal" [
      ("N37-PROV", "Consume exactly node [36]'s defect constructor."),
      ("N37-WITNESS", "Retain one original-interface context and the unequal exact responses there."),
      ("N37-SCOPE", "Mark precisely that target-defect residual terminal without inspecting the universal sibling."),
      ("N37-WORK", "Perform no new computation after the proof-level audit.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 38 "erdos.p13-curvature-proper-representative-decision" [
      ("N38-PROV", "Consume exactly node [36]'s original-interface universal constructor."),
      ("N38-LOCATION", "Decide exhaustively whether the retained final carrier equals the original atom or strictly enlarges it."),
      ("N38-REPRESENTATIVE", "Keep the representative indexed by the final carrier and transport it only on the equality edge."),
      ("N38-WORK", "Compare only the two stored support values; enumerate no support universe.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 39 "erdos.p13-curvature-proper-compression-terminal" [
      ("N39-PROV", "Consume node [38]'s literal at-original constructor and equality."),
      ("N39-TRANSPORT", "Transport the carrier representative to the original proper atom along that equality."),
      ("N39-CT3", "Execute the representative's stored CT3 compression and contradict minimality."),
      ("N39-WORK", "Use dependent equality transport and the stored compression theorem only.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 40 "erdos.p13-curvature-enlarged-support" [
      ("N40-PROV", "Consume node [38]'s literal strict-enlargement constructor."),
      ("N40-FOCUS", "Focus that active leaf while retaining all certificate properties in the accumulated ledger."),
      ("N40-SCOPE", "Add no new support object, property, or decision."),
      ("N40-WORK", "Use the framework focus operation with zero local checks.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 41 "erdos.p13-curvature-carrier-scope" [
      ("N41-PROV", "Consume the exact node-[40] carrier."),
      ("N41-SCOPE", "Classify that exact carrier by its stored proper-or-whole tag."),
      ("N41-YES", "Retain the proper constructor for node [42]."),
      ("N41-NO", "Retain the whole constructor for node [43]."),
      ("N41-WORK", "Perform no graph or support scan.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 42 "erdos.p13-curvature-proper-carrier-terminal" [
      ("N42-PROV", "Consume node [41]'s proper constructor on the identical enlarged carrier."),
      ("N42-INJECTIVE", "Use the admitted quotient's graph-owned proper-carrier injectivity theorem."),
      ("N42-CLOSE", "Contradict the retained distinct equal-code pair and close only this leaf."),
      ("N42-WORK", "Use one theorem application and the framework yes closure.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 43 "erdos.p13-curvature-whole-carrier" [
      ("N43-PROV", "Consume node [41]'s whole constructor directly, not through node [42]."),
      ("N43-TRANSPORT", "Transport whole-ness to the equal determination-certificate carrier using its stored carrier equality."),
      ("N43-CONTINUE", "Continue only the whole leaf through the framework."),
      ("N43-WORK", "Perform zero checks and introduce no new case.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 44 "erdos.p13-curvature-repair-identity" [
      ("N44-PROV", "Consume the exact node-[43] whole-carrier continuation."),
      ("N44-IDENTITY", "Derive the one--three repair identity from the handshake and connected cycle-rank equations, including the graph-component specialization."),
      ("N44-SCOPE", "Apply the identity only to a supplied component; enumerate no component family."),
      ("N44-WORK", "Use symbolic integer arithmetic on the supplied component only.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 45 "erdos.p13-curvature-closed-exact-barrier" [
      ("N45-PROV", "Consume the exact node-[44] output on node [43]'s whole-carrier leaf."),
      ("N45-INJECTIVE", "Use the admitted quotient's graph-owned whole-carrier theorem to prove its raw code injective."),
      ("N45-SCOPE", "Leave the contradiction with the retained collision to node [46]."),
      ("N45-WORK", "Enumerate no quotient, context, coordinate, or support family.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 46 "erdos.p13-curvature-rank-drop-terminal" [
      ("N46-PROV", "Consume node [45]'s exact injectivity theorem and node [35]'s retained collision."),
      ("N46-CONTRADICTION", "Apply injectivity to the equal quotient values of the two distinct raw coordinates and derive False."),
      ("N46-WORK", "Use one theorem application with no computation.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 47 "erdos.p13-curvature-full-rank-cross-panel" [
      ("N47-PROV", "Consume the exact node-[34] full-rank constructor on its separate diagram edge."),
      ("N47-RANK", "Retain the exact Node32FullRank proposition in the literal node-[34] stage rather than a copied node-[34] field."),
      ("N47-SEPARATION", "Do not consume node [37] or any rank-drop terminal."),
      ("N47-WORK", "Use the framework marker with zero scans.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 48 "erdos.forced-curvature-cost-split" [
      ("N48-PROV", "Consume the literal node-[47]/node-[34] full-rank leaf on the same accumulated residual."),
      ("N48-CONSTANTS", "Define the exact ordinary and high-entropy curvature-cost constants and the local error."),
      ("N48-WINDOW-FINITE", "Prove the ordinary finite accounting inequality on the exact leaf."),
      ("N48-HIGH-FINITE", "Prove the conditional high-entropy finite accounting inequality on the same leaf."),
      ("N48-COST", "Kernel-derive both ordinary and high-entropy forced-cost conclusions by positive scalar transport."),
      ("N48-WORK", "Use the framework map with zero local scans; the two finite accounting producers remain missing.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 49 "erdos.finite-remainder-state-entropy" [
      ("N49-PROV", "Consume the literal node-[48] output on its exact full-rank leaf."),
      ("N49-ATOM", "Define the fixed atom part inherited from R and require candidate subcubicity on it."),
      ("N49-P13", "Require componentwise P13-freeness through the equivalent whole-graph induced-P13-free predicate."),
      ("N49-CORE", "Require that every nonempty internal vertex set contains a vertex of internal degree at most two, i.e. that the candidate has no internal 3-core."),
      ("N49-CAP", "Bound the candidate positive net-deficiency numerator by the exact current numerator inherited from R; the support denominator is identical."),
      ("N49-FAMILY", "Define the paper's exact set G(R) of labelled simple graphs on V(R) satisfying all four already imposed constraints."),
      ("N49-ENTROPY", "Define eta(R)=log2|G(R)|/|R| from that exact family and expose it to node [50]."),
      ("N49-WORK", "Keep the family and its cardinality symbolic; perform zero semantic scans and enumerate no labelled-graph universe.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 50 "erdos.entropy-scale-split" [
      ("N50-PROV", "Retrieve the exact dependent node-[49] output from the accumulated ledger on the identical remainder and constrained graph family."),
      ("N50-THRESHOLD", "Define the original threshold (1/10)log2 n and compare it with the literal eta(R) from node [49]."),
      ("N50-YES", "Represent the original yes edge by (1/10)log2 n <= eta(R)."),
      ("N50-NO", "Represent the original no edge by eta(R) < (1/10)log2 n."),
      ("N50-EXHAUSTIVE", "Use the framework focused-branch decision so the two branches are exhaustive and add no third edge."),
      ("N50-WORK", "Use a proof-level ordered split with zero primitive checks; evaluate neither logarithms nor the constrained graph family.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 51 "erdos.high-remainder-bits" [
      ("N51-PROV", "Continue only the exact high constructor of the accumulated node-[50] decision on the identical node-[49] constrained graph family G(R)."),
      ("N51-ENTROPY", "Use node [49]'s exact identity eta(R)=log2|G(R)|/|R| without evaluating the constrained graph family."),
      ("N51-BITS", "Multiply the high-edge inequality by |R| and rewrite to obtain the manuscript bit contribution (|R|/10)log2 n <= log2|G(R)|."),
      ("N51-LOW", "Make no claim on the node-[50] low edge; that edge belongs to its separate node-[53] consumer."),
      ("N51-SCOPE", "Assert no same-context window/remainder realization, no node-[52] joint accounting, and no node-[54] entropy cap."),
      ("N51-WORK", "Perform no new finite scan; reuse node [50]'s zero-check ordered split and symbolic real arithmetic only.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 52
      "erdos.window-remainder-framework-handoff" [
      ("N52-PROV", "Consume node [51]'s exact high-entropy bit output on the identical accumulated residual."),
      ("N52-REGLUE", "Use the existing hot/cold aggregate's remainder-preserving reglue operation; absence remains the already declared cold outcome."),
      ("N52-JOINT", "Instantiate Core's symbolic base-plus-dependent-choice profile and prove that realized remainder states and all retained hot-window choices share one recoverable skeleton code."),
      ("N52-CAP", "Transport the exact joint cardinality bound through the aggregate's labelled-skeleton code-capacity theorem."),
      ("N52-POWER", "Instantiate Core's powered joint-normalization profile; retain discarded hot scales and all cold-window mass on the error side of the exact natural-number inequality."),
      ("N52-LOG-THETA", "Use Core's logarithmic transport and node [51]'s inherited remainder-bit lower bound to produce exactly the error-bearing joint budget whose strict reverse is closed at node [54]."),
      ("N52-ROUTE", "Map only the node-[51] high leaf; preserve every bypass and sibling branch through the framework."),
      ("N52-WORK", "Use only symbolic arithmetic and framework ledger composition; perform zero semantic inspections and no ambient-universe enumeration.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 54
      "erdos.node54-entropy-cap-closure" [
      ("N54-52-PROV", "Consume the literal node-[52] feasibility payload from the accumulated high edge while retaining node [50]'s low edge unchanged."),
      ("N54-52-STRICT", "Identify the finite high-theta alternative as the strict reverse of node [52]'s exact error-bearing cap."),
      ("N54-52-CLOSE", "Prove the strict node-[52] high-theta leaf impossible by symbolic order arithmetic."),
      ("N54-WORK", "Perform zero semantic checks and enumerate no graph, context, state, product, assignment, or Boolean universe.")
    ] ++ ExampleNodeObligationDescriptor.missing 54 [
      ("N54-SMALL-CAPACITY", "Prove the paper's independent-capacity theorem on node [53]'s exact strict-small leaf; this producer is missing and is not proved evidence.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 53
      "erdos.low-entropy-forced-cost-fit" [
      ("N53-PROV", "Consume only the exact low constructor of the accumulated node-[50] decision and preserve node [51]'s high output unchanged."),
      ("N53-BUDGET", "Define the remaining non-curvature budget from the exact labelled-skeleton, hot-window, and node-[49] constrained-family bit counts."),
      ("N53-COST", "Consume the inherited full-rank curvature cost without recomputing node [47] or node [48]."),
      ("N53-YES", "Retain the strict small-budget edge remainingBits < forcedCurvatureBits for node [54]."),
      ("N53-NO", "Retain the complementary large-budget edge forcedCurvatureBits <= remainingBits for node [55]."),
      ("N53-EXHAUSTIVE", "Use the framework no-after-yes continuation so both node-[53] edges are exhaustive on the literal node-[50] value."),
      ("N53-WORK", "Perform one proof-level real-order comparison and no graph, state, product, context, or Boolean-universe enumeration.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 55
      "erdos.large-budget-residual-handoff" [
      ("N55-PROV", "Consume the exact node-[53] complementary large-budget constructor after node [54] terminalizes the other two Part-IV leaves."),
      ("N55-MARKER", "Name the framework's already focused active value Residual C without constructing an application-owned output or handoff."),
      ("N55-BRANCH", "Expose exactly Residual C on the original node-[53] no edge, adding no inequality, density claim, case, or hypothesis."),
      ("N55-HANDOFF", "Preserve every terminal and earlier bypass while retrieving the identical focused stage through the framework."),
      ("N55-WORK", "Use zero-check framework routing and perform no mathematical recomputation or finite scan.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 56
      "erdos.large-budget-net-cap" [
      ("N56-PROV", "Consume only node [55]'s literal Residual C leaf on the same accumulated residual."),
      ("N56-DEFS", "Define the exact net-deficiency numerator, surplus error, and rational tau_win printed by the paper."),
      ("N56-FINITE", "Conditionally retain the previously verified finite error-bearing net cap through one certificate indexed by that exact leaf."),
      ("N56-QUARTER", "Evaluate the exact limiting coefficient tau_win symbolically and prove tau_win < 1/4."),
      ("N56-HANDOFF", "Continue only the focused active leaf through the framework and preserve every bypass automatically."),
      ("N56-WORK", "Perform zero local graph checks and no ambient-universe enumeration.")
    ] ++ ExampleNodeObligationDescriptor.missing 56 [
      ("N56-NETCAP", "Prove the node-[24]/[29] finite-cap theorem at the literal Residual C indices; this producer is missing and is not proved evidence.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 57
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N57-PROV", "Consume the exact node-[56] output from the accumulated ledger on the same eventual tail."),
      ("N57-STRICT", "Convert the normalized strict-quarter inequality to its exact denominator-free natural-number form without dropping the node-[56] error." )
    ] ++ ExampleNodeObligationDescriptor.provedForStep 58
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N58-CHARGE", "Define the manuscript net charge as the exact quarter-scaled integer numerator on the identical remainder.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 59
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N59-SPLIT", "Retain the strict negative constructor forced by node [57] on the exact node-[58] charge.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 60
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N60-CLOSE", "Contradict the nonnegative edge using the identical strict negative integer charge.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 61
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N61-DECOMP", "Use the canonical connected-component decomposition and its exact additive charge identity."),
      ("N61-CT11", "Run CT11 on that finite ordered component list and return an actual connected negative support." )
    ] ++ ExampleNodeObligationDescriptor.provedForStep 62
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N62-SPLIT", "Inspect only the selected support's actual high centers and return exactly the original Type-A or Type-B edge.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 63
      "erdos.type-a-nodes57-63-local-provenance" [
      ("N63-TYPE-A", "On the no-high-center edge, construct the exact subcubic Type-A support profile on the same localized support."),
      ("N63-WORK", "Bound the component and selected-support scans by twice the ambient vertex count.")
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
            "Node [6] stores the exact certificate decision. Node [7] interprets its C1 certificate as the official target, closes that terminal against inherited counterexample avoidance, and retains only the literal avoiding run. The K₄ run independently pins the positive path."
          declarations := [
            `Erdos64EG.Internal.runAvoidingCT1,
            `Erdos64EG.Internal.runMersenneCT1,
            `Erdos64EG.Internal.node6MersenneDecision,
            `Erdos64EG.Internal.node7CloseTarget,
            `Erdos64EG.Internal.node7PowerOfTwoCycle,
            `Erdos64EG.Internal.node7_avoids,
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
            `StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput.edgeRootedEncoding,
            `StructuralExhaustion.CT1.ResidualRefinement.DependentCertificateFamily.closePublicTargetContinueAvoidingUsingStage
          ]
        }
      ]
      scopeNotes :=
        "This covers nodes [5]--[7]. The C1 edge is the manuscript target terminal; the exact avoiding edge is the sole successor consumed by node [8]."
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
          declarations := [
            `Erdos64EG.Internal.node8NoProperCore,
            `Erdos64EG.Internal.node8_noProperCore
          ]
        },
        {
          groupId := "proper-core-execution"
          title := "Certified CT2 execution audit"
          role := .executionAudit
          explanation :=
            "These declarations prove the exact deletion-C2 terminal, typed trace, totality, one-check count, and constant polynomial budget for the supplied proper-subgraph certificate."
          declarations := [
            `Erdos64EG.Internal.node8_ct2_certificate,
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
            "The node consumes the sole avoiding successor left by node [7]. Framework dependent-successor storage retains the exact CT1 run and selected context; no root-level prefix is reconstructed."
          declarations := [
            `Erdos64EG.Internal.Node7Stage,
            `Erdos64EG.Internal.Node8Stage,
            `Erdos64EG.Internal.runInitialThroughNode8
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
          groupId := "node9-deletion-criticality"
          title := "Node [9] deletion-criticality successor"
          role := .semanticTheorem
          explanation :=
            "The literal node-[8] successor is consumed once. The graph-owned local deletion theorem supplies exactly the degree-three endpoint alternative, which node [9] appends to the accumulated ledger."
          declarations := [
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.deletionCriticalityFacts,
            `Erdos64EG.Internal.node9DeletionCriticality,
            `Erdos64EG.Internal.node9_everyEdgeTouchesDegreeThree,
            `Erdos64EG.Internal.runInitialThroughNode9
          ]
        },
        {
          groupId := "node10-high-degree-independence"
          title := "Node [10] high-degree independence"
          role := .semanticTheorem
          explanation :=
            "Node [10] consumes the exact endpoint theorem stored by node [9] and applies the reusable graph-local consequence; it does not rerun deletion or inspect an ambient family."
          declarations := [
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.slackVerticesIndependent_of_tightEndpoint,
            `Erdos64EG.Internal.node10HighDegreeIndependence,
            `Erdos64EG.Internal.node10_highDegreeVerticesIndependent,
            `Erdos64EG.Internal.runInitialThroughNode10
          ]
        },
        {
          groupId := "criticality-ledger"
          title := "Single-ledger provenance"
          role := .compositionProvenance
          explanation :=
            "Framework dependent successors retain each literal predecessor and append only the new node-local proposition. No application handoff or route object is present."
          declarations := [
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapStage,
            `Erdos64EG.Internal.Node9Stage,
            `Erdos64EG.Internal.Node10Stage
          ]
        }
      ]
      scopeNotes :=
        "This is exactly nodes [9] and [10]. Each theorem is pointwise on the supplied edge or adjacent pair; no graph, path, context, state, or universe family is enumerated."
      workBound := "Zero new primitive checks; both nodes reuse the graph-owned symbolic deletion theorem."
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
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.ofTargetComplete,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible,
            `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.targetDefective_of_not_contextEquivalent,
            `Erdos64EG.Internal.node11_boundaryDegreeProfile,
            `Erdos64EG.Internal.node12_context_universal,
            `Erdos64EG.Internal.node13_replacement,
            `Erdos64EG.Internal.node14_uncompressible
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
          title := "Literal node-[11]--[14] chain"
          role := .compositionProvenance
          explanation :=
            "Each node consumes only its literal immediate predecessor through the one accumulated ledger and appends only its own mathematical responsibility."
          declarations := [
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapStage,
            `Erdos64EG.Internal.node11BoundariedAtoms,
            `Erdos64EG.Internal.node12ContextUniversality,
            `Erdos64EG.Internal.node13Replacement,
            `Erdos64EG.Internal.node14Uncompressibility,
            `Erdos64EG.Internal.runInitialThroughNode11,
            `Erdos64EG.Internal.runInitialThroughNode12,
            `Erdos64EG.Internal.runInitialThroughNode13,
            `Erdos64EG.Internal.runInitialThroughNode14
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
        "This descriptor covers only nodes [11]--[14]: boundaried atoms, context universality, replacement, and hereditary target-uncompressibility. Later rank-dependence nodes consume these facts from the ledger but are tracked by their own descriptors."
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
          groupId := "p13-node15-decision"
          title := "Node [15] exhaustive P₁₃-free decision"
          role := .semanticTheorem
          explanation :=
            "The framework retrieves the literal node-[14] stage once and stores the exact P₁₃-free or non-P₁₃-free constructor on that same selected graph."
          declarations := [
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideUsingStage,
            `Erdos64EG.Internal.node15P13Decision,
            `Erdos64EG.Internal.node15_exhaustive,
            `Erdos64EG.Internal.runInitialThroughNode15,
            `Erdos64EG.Internal.node15LocalChecks_eq_zero
          ]
        },
        {
          groupId := "p13-node16-hss-terminal"
          title := "Node [16] HSS target terminal"
          role := .semanticTheorem
          explanation :=
            "HSS turns exactly node [15]'s yes constructor into the official target, which contradicts the target-avoidance theorem already carried by the same minimal-counterexample context."
          declarations := [
            `Erdos64EG.Internal.hssTarget_of_p13Free,
            `Erdos64EG.Internal.node16_hss_target,
            `Erdos64EG.Internal.node16_hss_closure,
            `Erdos64EG.Internal.node16HSSContinuation,
            `Erdos64EG.Internal.runInitialThroughNode16,
            `Erdos64EG.Internal.node16LocalChecks_eq_zero
          ]
        },
        {
          groupId := "p13-node15-16-provenance"
          title := "Literal decision and surviving no edge"
          role := .compositionProvenance
          explanation :=
            "`closeDependentDecisionYes` eliminates only the HSS terminal and retains node [15]'s literal no constructor for node [17]. No path witness, route, or new branch is manufactured here."
          declarations := [
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes,
            `Erdos64EG.Internal.Node15Stage,
            `Erdos64EG.Internal.Node16Stage
          ]
        }
      ]
      scopeNotes :=
        "The corollary is fully formalized relative to the explicitly isolated HSS theorem. The app must display that trust boundary separately from kernel-proved consequences."
      workBound := "Zero node-local scans: one proof-level exact dichotomy and the isolated HSS theorem; no path, tuple, graph, or context universe is materialized."
    },
    {
      stepId := "erdos.p13-packing"
      stageId? := some "proof-slice.p13-packing"
      title := "Maximal induced-P₁₃ packing"
      plainExplanation :=
        "On node [16]'s literal not-P₁₃-free survivor, CT12 selects a deterministic vertex-disjoint induced-P₁₃ list and proves it maximal by saturation. The public node-[17] output deliberately makes no maximum-cardinality or remainder claim."
      formalStatement :=
        "\\mathcal P\\text{ is vertex-disjoint and maximal among induced }P_{13}\\text{ families}"
      status := .implemented
      correspondence := .composite
      manuscriptRefs := [
        { label := "def:p13-packing", title := "Maximal induced-P₁₃ packing", nodeIds := [17] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node17-maximal"
          title := "Node [17] maximal packing semantics"
          role := .semanticTheorem
          explanation :=
            "The selected list is nonempty, support-nodup, pairwise disjoint, and saturated: every induced P₁₃ meets a selected window. Saturation is the diagram's maximality assertion and does not imply or expose maximum cardinality."
          declarations := [
            `Erdos64EG.Internal.node17_maximal,
            `Erdos64EG.Internal.node17_nonempty,
            `Erdos64EG.Internal.Node17Output
          ]
        },
        {
          groupId := "p13-node17-execution"
          title := "Node [17] CT12 execution"
          role := .executionAudit
          explanation :=
            "The framework owns the maximal-only verified stage and retains the exhausted terminal, typed trace, totality, and selected-list polynomial work certificate."
          declarations := [
            `Erdos64EG.Internal.node17InducedP13Packing,
            `Erdos64EG.Internal.node17_terminal,
            `Erdos64EG.Internal.node17Total,
            `Erdos64EG.Internal.node17WorkBudget,
            `Erdos64EG.Internal.runInitialThroughNode17
          ]
        },
        {
          groupId := "p13-node17-provenance"
          title := "Literal survivor and public cursors"
          role := .compositionProvenance
          explanation :=
            "Node [17] consumes exactly node [16]'s surviving no constructor. Public accessors expose the identical graph, selected window list, and its length without reconstructing an older prefix."
          declarations := [
            `Erdos64EG.Internal.Node17Stage,
            `Erdos64EG.Internal.Node17StageContext,
            `Erdos64EG.Internal.node17Windows,
            `Erdos64EG.Internal.node17PackingNumber
          ]
        }
      ]
      scopeNotes :=
        "This descriptor covers only node [17]. Remainder construction and every quantitative packing consequence belong to later diagram nodes and are not front-loaded here."
      workBound := "One framework-selected maximal-list audit with work linear in the selected list; no family of packings, graph universe, or maximum-cardinality search is materialized."
    },
    {
      stepId := "erdos.p13-labels"
      stageId? := some "proof-slice.p13-labels"
      title := "Exact P₁₃ attachment-label algebra"
      plainExplanation :=
        "An outside vertex is labelled by the path positions to which it is adjacent. Target avoidance forbids pairs of positions at gaps two and six. Two parity automata symbolically count the seven size fibres and transport the exact 399-row carrier into CT10; no global code scan is used for the count."
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
            `Erdos64EG.Internal.P13ParityLabelCount.gapSafeSized13_natCard_eq_convolution,
            `Erdos64EG.Internal.P13ParityLabelCount.gapLegal13_natCard,
            `Erdos64EG.Internal.symbolicLegalP13Labels_card,
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
            "The node-[18] output proves directly that every actual nonempty attachment to an induced P₁₃ in the retained node-[17] graph has a legal label."
          declarations := [
            `Erdos64EG.Internal.Node18Output.actualLabelsLegal
          ]
        },
        {
          groupId := "label-provenance"
          title := "Label-algebra endpoint and predecessor"
          role := .compositionProvenance
          explanation :=
            "The framework successor consumes the literal node-[17] maximal-packing stage. Its public cursor exposes the identical selected graph to node [19] without a copied prefix or custom route."
          declarations := [
            `Erdos64EG.Internal.Node18Stage,
            `Erdos64EG.Internal.Node18Output,
            `Erdos64EG.Internal.Node18StageContext,
            `Erdos64EG.Internal.node18P13LabelAlgebra,
            `Erdos64EG.Internal.runInitialThroughNode18,
            `Erdos64EG.Internal.node18LocalChecks_eq
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
        "Node [18]'s legal-label table and Cₛ/Ω₂ definitions are implemented. Node [21]'s 91-barrier interface is tracked separately and remains yellow until its legacy packed-row and safe/flat count audits are sole-HSS clean."
      workBound := "The fixed local CT10 table records 167792 primitive checks. The 399 count and seven size fibres are transported symbolically from the parity automata; no ambient graph or universe of packings is enumerated."
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
        title := "Framework-owned squared-scale decision and strict branch name"
        role := .semanticTheorem
        explanation := "Node [19] supplies only the actual surplus, graph order, and fixed coefficient to the reusable ordered split. Node [20] is definitionally its strict constructor and adds no mathematics before node [125]."
        declarations := [
          `Erdos64EG.Internal.node19SurplusCoefficient,
          `Erdos64EG.Internal.node19Profile,
          `Erdos64EG.Internal.node19Family,
          `Erdos64EG.Internal.Node19High,
          `Erdos64EG.Internal.Node19Low,
          `Erdos64EG.Internal.Node19Stage,
          `Erdos64EG.Internal.node19SurplusScaleDecision,
          `Erdos64EG.Internal.runInitialThroughNode19,
          `Erdos64EG.Internal.node19_exhaustive,
          `Erdos64EG.Internal.node19WorkBudget,
          `Erdos64EG.Internal.node19_work_zero,
          `Erdos64EG.Internal.Node20Entry,
          `Erdos64EG.Internal.Node20SourceStage,
          `Erdos64EG.Internal.node20Entry_iff_node19High,
          `Erdos64EG.Internal.node20LocalChecks_eq_zero
        ]
      }]
      scopeNotes := "Nodes [19] and [20] are proved locally. Node [20] only names the strict constructor; its surplus-pair mathematics begins at the existing node-[125] expansion. The bounded constructor's node-[21] producer remains missing."
      workBound := "Zero graph scans: one exact symbolic natural-number comparison and no square root, floating-point computation, graph family, or threshold search."
    },
    {
      stepId := "erdos.p13-multiscale-curvature"
      stageId? := some "proof-slice.p13-multiscale-curvature"
      title := "Node-[21] multi-scale curvature output interface"
      plainExplanation := "The lightweight API fixes the exact CT10 classification, packed relation profile, safe/flat products, work expression, and complete node-[21] output type on node [19]'s bounded edge. Its optimized semantic/count producer remains yellow; downstream nodes use the identical typed output provisionally."
      formalStatement := "|\\{(a,b):a,b\\ge1,\\ a+b\\le14\\}|=91,\\qquad 2^{118}\\prod F_{a,b}<\\prod S_{a,b}"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "lem:curv-enum", title := "Finite curvature enumeration", nodeIds := [21] },
        { label := "app:curv-code", title := "Curvature computation", nodeIds := [21] }
      ]
      declarationGroups := [{
        groupId := "multiscale-node21-api"
        title := "Exact conditional node-[21] API"
        role := .compositionProvenance
        explanation := "These declarations define the complete paper-local result and its literal framework continuation while the optimized producer is repaired independently."
        declarations := [
          `Erdos64EG.Internal.Node21Output,
          `Erdos64EG.Internal.P13BarrierAccepted,
          `Erdos64EG.Internal.p13BarrierClassification,
          `Erdos64EG.Internal.p13MultiScaleBarrierProfile,
          `Erdos64EG.Internal.p13BarrierSafeCount,
          `Erdos64EG.Internal.p13BarrierFlatCount,
          `Erdos64EG.Internal.p13BarrierSafeProduct,
          `Erdos64EG.Internal.p13BarrierFlatProduct,
          `Erdos64EG.Internal.p13MultiScaleCheckCount,
          `Erdos64EG.Internal.Node21Context,
          `Erdos64EG.Internal.Node21Stage
        ]
      }]
      scopeNotes := "Node [21] remains yellow. The API is exact, but its complete semantic/count producer has not yet replaced the provisional old output."
      workBound := "Fifteen fixed 399×399 bit relations and 91 quadratic barrier scans, split into 15 independently cached audit shards. The public CT10 classification uses 196 candidate checks; no graph family or Boolean cube is enumerated."
    },
    {
      stepId := "erdos.p13-weighted-live-cold"
      stageId? := some "proof-slice.p13-weighted-live-cold"
      title := "Weighted live/cold same-window handoff"
      plainExplanation := "The original safe/flat strategy is formalized as a sequential conditional-fibre package with coordinate-dependent factors. Failure retains the identical selected window. The negative list is filtered without substitution by the ambient-cubic predicate; each retained entry owns exactly fifteen external stubs, drops its two transit stubs, and passes exactly thirteen selected excess incidences to the corridor runner."
      formalStatement := "\\mathcal P=\\mathcal P_{\\rm hot}\\sqcup\\mathcal P_{\\rm cold},\\qquad |\\mathcal E_{\\rm br}|=13|\\mathcal P_{\\rm cold}^{\\rm cub}|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "rem:p13-weighted-live-cold-handoff", title := "Formal weighted live/cold and branch-excess handoff", nodeIds := [145, 151, 152, 153] }
      ]
      declarationGroups := [{
        groupId := "p13-weighted-live-cold-provenance"
        title := "Exact weighted package or same-window cold residual"
        role := .compositionProvenance
        explanation := "The variable-factor ledger telescopes the 91 safe/flat factors. The packing-order runner carries a dependent joint state with recoverable local choices and a bounded injective spine code. Each failed compatible extension retains its exact prior aggregate and window; that sequential rejection list is consumed by the cold corridor runner."
        declarations := [
          `StructuralExhaustion.Core.VariableConditionalFibreProductCost.Profile.complete_product_le,
          `StructuralExhaustion.Core.VariableConditionalFibreProductCost.Profile.checks_le_state_mul_coordinate,
          `Erdos64EG.Internal.P13WeightedLiveWindowPackage,
          `Erdos64EG.Internal.P13WeightedLiveWindowPackage.product_le,
          `Erdos64EG.Internal.P13WeightedLiveWindowPackage.checks_local,
          `Erdos64EG.Internal.P13WeightedHotWindow,
          `StructuralExhaustion.Core.SequentialCompatibleExtensionLedger.run,
          `Erdos64EG.Internal.P13SequentialHotAggregate,
          `Erdos64EG.Internal.P13SequentialCompatibleExtension,
          `Erdos64EG.Internal.P13SequentialWeightedColdWindow,
          `Erdos64EG.Internal.p13SequentialFinal_localProduct_le_fixedCapacity,
          `Erdos64EG.Internal.p13SequentialFinal_retainedCount,
          `Erdos64EG.Internal.p13SequentialWeightedHotCount_add_coldCount,
          `Erdos64EG.Internal.p13SequentialWeightedColdWindows_window_nodup,
          `Erdos64EG.Internal.p13SequentialHotBudget_total_le_budget_add_cold,
          `Erdos64EG.Internal.p13WeightedCold_cubic_nonCubic_length,
          `Erdos64EG.Internal.p13WeightedColdNonCubic_length_le_totalSurplus,
          `Erdos64EG.Internal.p13WeightedColdNonCubic_length_sq_le_nearCubicBudget,
          `Erdos64EG.Internal.p13WeightedColdBranchExcessStubs_length,
          `Erdos64EG.Internal.p13WeightedColdBranchExcessStubs_nodup,
          `Erdos64EG.Internal.P13WeightedColdBranchExcessStub.sameWindow,
          `Erdos64EG.Internal.p13WeightedColdBranchExcessSchedule_length,
          `Erdos64EG.Internal.p13WeightedColdBranchExcessSchedule_nodup,
          `Erdos64EG.Internal.p13WeightedColdRestrictedEntries_sources,
          `Erdos64EG.Internal.p13WeightedColdRestrictedEntries_sources_nodup,
          `Erdos64EG.Internal.p13WeightedColdRestrictedComponentSchedule_sources,
          `Erdos64EG.Internal.p13WeightedColdRestrictedComponentSchedule_sources_nodup,
          `Erdos64EG.Internal.thirteen_mul_weightedCold_le_branchExcess_add_surplus,
          `Erdos64EG.Internal.verifiedP13WeightedColdNearCubicPayment,
          `Erdos64EG.Internal.P13WeightedColdBranchExcessStub.corridor
        ]
      }]
      scopeNotes := "This verifies the accumulated compatible-extension interface, dependent joint-state capacity, exact sequential cold cubic/non-cubic partition, the injection of every discarded non-cubic cold window into a distinct inherited surplus unit, the exact node-[21] square-root budget on that loss, and the duplicate-free fifteen-to-thirteen branch-excess schedule. The complete node-[152]-to-[153] classifier retains the identical source schedule exactly once across both original component and cross-window outcomes. On the existing component outcome it constructs the actual restricted outside connected component, the literal cyclic successor stub, and a declared-order shortest return corridor; the cross-window outcome is preserved unchanged. The manuscript's stronger lexicographically first simple-path selector and the graph-owned terminal ColdBoundedGerm producer remain open."
      workBound := "The proof-level extension split traverses the declared packing once. Package checks and all cold geometry remain local; no ambient graph, context, state-subset, or Boolean universe is enumerated."
    },
    {
      stepId := "erdos.type-a-nodes57-63-local-provenance"
      stageId? := some "proof-slice.type-a-nodes57-63-local-provenance"
      title := "Nodes [57]--[63] local Type-A chain"
      plainExplanation := "The accumulated node-[56] cap yields the exact strict-quarter inequality on its proved eventual tail. The framework attaches that fact once, retains the exact integer net charge, and CT11 scans only the canonical component schedule to select a negative connected support. Node [62] then returns only the paper's Type-A or Type-B route."
      formalStatement := "[56]\\Longrightarrow[57]\\Longrightarrow[58]\\Longrightarrow[59]\\Longrightarrow[61]\\Longrightarrow([63]\\text{ or }[64])"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "fig:proof-diagram-part-v", title := "Large-budget discharge chain", nodeIds := [57, 58, 59, 60, 61, 62, 63] }]
      declarationGroups := [{
        groupId := "type-a-57-63-local-chain"
        title := "Exact accumulated chain and linear CT11 schedule"
        role := .compositionProvenance
        explanation := "The indexed payloads preserve each immediate predecessor and the identical remainder/support; the only scan is the canonical component list plus the selected support."
        declarations := [
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node57_eventually,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.strictQuarterNat_of_normalized,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node57Refinement,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node58Refinement,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node59Refinement,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node60_impossible,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node61Refinement,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.node62,
          `Erdos64EG.Internal.TypeANodes57To63Provenance.localChecks_linear
        ]
      }]
      scopeNotes := "The strict-quarter step is explicitly eventual, exactly as in the manuscript's o(|R|) statement; no error-free finite claim is made. No new node, edge, or case is introduced."
      workBound := "One canonical component scan plus one selected-support degree scan; at most twice the ambient vertex count."
    },
    {
      stepId := "erdos.type-a-nodes86-88-local-thresholds"
      stageId? := some "proof-slice.type-a-nodes86-88-local-thresholds"
      title := "Nodes [86]--[88] local Type-A thresholds"
      plainExplanation := "Given the exact node-[63] Type-A residual, Lean derives zero assigned surplus and strict quarter deficiency, obtains diameter at most eleven from P13-freeness, applies the local subcubic Moore count, and computes the three receiver thresholds. The predecessor is not yet green, so these are conditional local contracts."
      formalStatement := "[63]\\Longrightarrow \\sigma(X)=0,\\ 4\\operatorname{def}^{+}(X)<|X|,\\ |X|\\le6142,\\ H_j=4(j+1)"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [{ label := "fig:proof-diagram-part-viii", title := "Type-A threshold chain", nodeIds := [86, 87, 88] }]
      declarationGroups := [{
        groupId := "type-a-86-88-local-thresholds"
        title := "Conditional diameter, Moore, and threshold proofs"
        role := .compositionProvenance
        explanation := "All objects are indexed by the identical selected support. The Moore proof uses one proof-selected shortest path and a bounded BFS/layer schedule, never a graph universe."
        declarations := [
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node86,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.VerifiedNode86Residual.assignedSurplus_eq_zero,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.VerifiedNode86Residual.four_deficiency_lt_card,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_p13Free,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_diameterAtMostEleven,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87_supportCardAtMost6142_of_diameter,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node87Checks_polynomial,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.q,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.threshold,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node88,
          `Erdos64EG.Internal.TypeANodes86To88Thresholds.node88Checks_constant
        ]
      }]
      scopeNotes := "Nodes [86]--[88] remain yellow solely because their immediate dependency chain begins at yellow node [63]. The declarations create no alternate route."
      workBound := "A quadratic local BFS/layer envelope for node [87], then three fixed arithmetic checks at node [88]."
    },
    {
      stepId := "erdos.type-a-node89-local-saturation"
      stageId? := some "proof-slice.type-a-node89-local-saturation"
      title := "Node [89] local receiver-saturation decision"
      plainExplanation := "The exact node-[88] support defines canonical receiver traces and their loads. One exhaustive local decision returns the existing unsaturated edge to node [90] or a literal saturated receiver on the existing edge to node [93]."
      formalStatement := "(\\forall w,\\ L(w)\\le4q(w)-1)\\quad\\text{or}\\quad(\\exists w,\\ L(w)\\ge4q(w))"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [{ label := "fig:proof-diagram-part-viii", title := "Type-A saturation decision", nodeIds := [89] }]
      declarationGroups := [{
        groupId := "type-a-89-local-saturation"
        title := "Exact conditional receiver-fibre dichotomy"
        role := .executionAudit
        explanation := "Both payloads retain the literal node-[88] input. The runner scans only actual support vertices and their canonical receiver fibres and exposes a polynomial work certificate."
        declarations := [
          `Erdos64EG.Internal.TypeANode89SaturationDecision.run,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.input,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.routing,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.routedReceiver_eq_canonical,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.ToNode93,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.ToNode90,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.run_exhaustive,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.localCheckCount_polynomial,
          `Erdos64EG.Internal.TypeANode89SaturationDecision.workBudget
        ]
      }]
      scopeNotes := "The eight local obligations are implemented conditionally, but node [89] remains yellow because node [88] is not reachable from a green predecessor."
      workBound := "One receiver test per support vertex and one actual cubic-source/receiver fibre comparison; quadratic local envelope."
    },
    {
      stepId := "erdos.p13-node153-produced-support-coverage"
      stageId? := some "proof-slice.p13-node153-produced-support-coverage"
      title := "Node [153] prior produced-support coverage"
      plainExplanation := "The ordinary Type-B occurrence schedule and the node-[84] grouped/extracted schedules populate one persistent, occurrence-indexed ledger. Equal event values remain distinct occurrences. F4 scans and filters this exact occurrence ledger directly, so no detached event list is created."
      formalStatement := "\\operatorname{Occ}(L_{F4})=\\operatorname{Occ}(L_{\\rm ord})\\uplus\\operatorname{Occ}(L_{\\rm dec})\\uplus\\operatorname{Occ}(L_8)"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [{ label := "def:cold-corridor-first-failure", title := "Cold corridor F4 produced-support test", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-node153-produced-support-coverage"
        title := "Persistent occurrence-preserving three-family aggregation"
        role := .compositionProvenance
        explanation := "The reusable Core ledger owns occurrence identity, append, restriction, dependent views, and exact finite checks. The Graph view recognizes the first exact support occurrence and proves total absence occurrence-by-occurrence. The Erdős layer only supplies the three event constructors and their declared supports."
        declarations := [
          `StructuralExhaustion.Core.FiniteResidualLedger.Ledger,
          `StructuralExhaustion.Core.ResidualRefinement.Ledger.append,
          `StructuralExhaustion.Core.ResidualRefinement.Ledger.require,
          `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.activeOccurrences,
          `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.activeOccurrences_card_le_occurrences,
          `StructuralExhaustion.Graph.FiniteResidualSupportLedger.View.recognize_exact,
          `StructuralExhaustion.Graph.ResidualSupportRefinement.Profile.recognize_exact,
          `StructuralExhaustion.Graph.ResidualSupportRefinement.Profile.FirstHit.get,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedger.PersistentLedger.recognize_exact,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.persistentBase,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.persistentBase_event_origin,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.CompleteState,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.ordinaryOccurrence_mem,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.decoratedOccurrence_mem,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.routeEightOccurrence_mem,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.outside_all_produced_occurrences,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_completeProducedLedger
        ]
      }]
      scopeNotes := "The aggregation and F4 recognition are exact relative to their producer occurrences, including duplicate event values. Node [153] remains yellow because the immutable manuscript flow supplies no pre-node-[24] graph-owned schedule of the later node-[64]/[84]/[108] occurrences, and the ColdBoundedGerm producer remains open. Candidate components are not substituted for actual produced occurrences."
      workBound := "Linear in the three actual producer schedules; no support deduplication or ambient universe scan."
    },
    {
      stepId := "erdos.p13-node153-exact-continuation"
      stageId? := some "proof-slice.p13-node153-exact-continuation"
      title := "Node [153] exact local F2--F5 continuation"
      plainExplanation := "For a supplied local corridor survivor, the runner tests the manuscript's F1 through F4 predicates in stage order. If every stored stage is clear, the actual corridor execution yields exactly the original F5 terminal or repeated support."
      formalStatement := "\\operatorname{scan}_{s\\in S}(F1,F2,F3,F4);\\ \\text{if clear, return }F5_{\\rm terminal}\\text{ or }F5_{\\rm repeat}"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "def:cold-corridor-first-failure", title := "Cold structural corridor and first-failure scan", nodeIds := [153] }
      ]
      declarationGroups := [{
        groupId := "p13-node153-exact-local-continuation"
        title := "Exact conditional F2--F5 runner"
        role := .executionAudit
        explanation := "F2 retains one proof-selected distinguishing context rather than scanning a context universe; F3 requires universal response and a proper representative; F4 reuses the inherited produced-support event; the clear branch runs the literal structural corridor."
        declarations := [
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.runExactContinuation,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.StageF2,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.StageF3,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.ExactF5,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.f4_absent,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.repeatedStageF2,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.repeatedStageF3,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactF5OfClear,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactLaterSemantics,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.runExactContinuation_total,
          `Erdos64EG.Internal.P13WeightedColdRestrictedPrefixPackage.exactContinuation_checks,
          `Erdos64EG.Internal.P13ProducedPriorSupportLedgerCoverage.P13WeightedColdRestrictedPrefixPackage.exists_localCorridorSurvivor_of_completeProducedLedger
        ]
      }, {
        groupId := "p13-node153-restricted-component-corridor"
        title := "Actual component and lexicographically first simple corridor"
        role := .compositionProvenance
        explanation := "The restricted-component schedule exposes the actual connected component and genuine cyclic List.next successor. The thin Erdős specialization instantiates the reusable finite lex-first path profile on exactly that component and those endpoints, proving simplicity, exact source and target, absence of an earlier simple path, and the local carrier bound."
        declarations := [
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath,
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_isPath,
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_head,
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_getLast,
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.no_earlier_path,
          `StructuralExhaustion.Graph.FiniteLexFirstSimplePath.Profile.firstPath_length_lt,
          `Erdos64EG.Internal.restricted_component_payload,
          `Erdos64EG.Internal.restricted_component_declaredOrderCorridor,
          `Erdos64EG.Internal.p13RestrictedLexFirstCorridorProfile,
          `Erdos64EG.Internal.p13RestrictedLexFirstCorridor,
          `Erdos64EG.Internal.restricted_component_lexFirstCorridor
        ]
      }]
      scopeNotes := "The actual restricted component and lex-first corridor are proved on the existing component edge. The three-family aggregation and exact LocalCorridorSurvivor connector remain relative to their producer schedules; node [153] stays yellow until the graph-owned complete ordinary node-[64] schedule, unconditional node-[84] realization, and ColdBoundedGerm producer are supplied."
      workBound := "The selected corridor has edge length below its supplied component cardinality, followed by one scan of the literal stored stage list. Distinguishing contexts are proof-selected; no ambient graph or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-node154-local-classifier"
      stageId? := some "proof-slice.p13-node154-local-classifier"
      title := "Node [154] local G1--G3 exhaustiveness and work"
      plainExplanation := "Given one bounded germ, the classifier checks its already supplied dyadic hit first. Only a negative hit check enables the exact finite response-code scan, which returns the first distinction or proves neutrality and constructs the silent exchange."
      formalStatement := "G1\\;\\vee\\;G2\\;\\vee\\;G3,\\qquad W_{154}\\le |\\mathcal C_{\\rm germ}|+1"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [{ label := "def:cold-bounded-germ", title := "Cold germ classifier", nodeIds := [154] }]
      declarationGroups := [{
        groupId := "p13-node154-local-priority-classifier"
        title := "Exact G1--G3 priority trace and local work"
        role := .executionAudit
        explanation := "The reusable Core ledger counts one optional-hit test and at most one pass over the supplied code schedule. The Erdős instantiation proves all three original constructors exhaustive with their exact trace; symbolic coverage handles arbitrary outside contexts without enumerating them."
        declarations := [
          `StructuralExhaustion.Core.FinitePriorityOptionScanWork.trace,
          `StructuralExhaustion.Core.FinitePriorityOptionScanWork.checks,
          `StructuralExhaustion.Core.FinitePriorityOptionScanWork.checks_le_codes_add_one,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classify,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyTrace,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyTrace_length_le_three,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyChecks,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classifyChecks_le_codes_add_one,
          `Erdos64EG.P13ColdGermLedger.ColdBoundedGerm.classify_exhaustive_with_trace
        ]
      }]
      scopeNotes := "This proves only the local node-[154] classifier contract for a supplied ColdBoundedGerm. The graph-owned node-[153] producer and equal-length/length-changing routing obligations XI-154-01/02 remain open."
      workBound := "At most one literal-hit check plus one pass over the declared finite germ response-code schedule; no ambient context, graph, piece, or completion universe is enumerated."
    },
    {
      stepId := "erdos.p13-node146-route8-threshold"
      stageId? := some "proof-slice.p13-node146-route8-threshold"
      title := "Exact node [146] route-8 threshold"
      plainExplanation := "The exact node-[145] ledger is preserved while one natural-number comparison decides whether the packing density is below 1/78. The yes payload proves the denominator-safe tau bound and routes to node [147]; the no payload proves theta is at least 1/78 and routes to node [148]."
      formalStatement := "78p_{13}<n\\iff\\theta<\\frac1{78}\\iff\\tau(\\theta)<\\frac3{13}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:cold-window-ledger", title := "Route-8 density threshold", nodeIds := [146] }
      ]
      declarationGroups := [{
        groupId := "p13-node146-threshold"
        title := "Exact threshold decision and both typed routes"
        role := .executionAudit
        explanation := "The runner derives positivity of the actual graph order from the inherited minimum-degree baseline, proves the two rational equivalences without dividing by a nonpositive denominator, and returns exactly the two original outgoing payloads with constant work."
        declarations := [
          `Erdos64EG.Internal.p13Node146AccumulatedRun,
          `Erdos64EG.Internal.p13PackingTheta,
          `Erdos64EG.Internal.p13Route8Tau,
          `Erdos64EG.Internal.p13VertexCount_pos,
          `Erdos64EG.Internal.p13Route8BelowThreshold_iff_theta,
          `Erdos64EG.Internal.p13Route8Tau_lt_three_thirteenths_iff,
          `Erdos64EG.Internal.p13Route8_denominator_pos_of_below,
          `Erdos64EG.Internal.P13Node146To147,
          `Erdos64EG.Internal.P13Node146To148,
          `Erdos64EG.Internal.p13Node146DecisionRefinement,
          `Erdos64EG.Internal.p13Node146LocalCheckCount_polynomial,
          `Erdos64EG.Internal.p13Node146WorkBudget,
          `Erdos64EG.Internal.p13Node146WorkBudget_checks
        ]
      }]
      scopeNotes := "This is exactly node [146]. It does not assume or prove the node-[147] private-carrier collision or the node-[148] hot-entropy decision."
      workBound := "One comparison of 78 p13 with n; constant primitive-check budget and no graph, context, state, or assignment enumeration."
    },
    {
      stepId := "erdos.p13-node147-private-carrier-arithmetic"
      stageId? := some "proof-slice.p13-node147-private-carrier-arithmetic"
      title := "Node [147] private-carrier arithmetic prefix"
      plainExplanation := "The accumulated node-[146] yes residual proves the strict coefficient gap needed by the private-carrier squeeze. CT4 proves the reusable private-carrier no-overcounting inequality, but the Type-A route-8 collection and canonical carrier-core stage from nodes [109]--[114] have not yet reached this node, so the terminal contradiction is not claimed."
      formalStatement := "\\tau(\\theta)<\\frac3{13}\\Longrightarrow\\tau(\\theta)<12\\left(\\frac14-\\tau(\\theta)\\right)"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "thm:large-budget-route8-only", title := "Route-8 private-carrier closure", nodeIds := [147] }
      ]
      declarationGroups := [{
        groupId := "p13-node147-arithmetic"
        title := "Dependency-ready strict collision margin"
        role := .executionAudit
        explanation := "This proves exactly the arithmetic prefix available from node [146] and records zero new local scans. It deliberately does not manufacture the absent carrier ledger."
        declarations := [
          `Erdos64EG.Internal.p13Node147ArithmeticPrefix,
          `Erdos64EG.Internal.p13Node147ArithmeticRefinement,
          `Erdos64EG.Internal.P13Node147ArithmeticPrefix,
          `Erdos64EG.Internal.p13Route8CollisionCoefficientGap,
          `Erdos64EG.Internal.p13Route8CollisionMargin_pos,
          `StructuralExhaustion.CT4.PrivateCarrierProfile.slot_mul_entry_le_carrier,
          `Erdos64EG.Internal.P13Route8PrivateCarrierLedger.three_mul_entries_le_carriers,
          `Erdos64EG.Internal.p13Node147ArithmeticCheckCount_polynomial
        ]
      }]
      scopeNotes := "Four of nine audited node-[147] obligations are proved. The five structural route-8 carrier obligations remain explicit in the web ledger."
      workBound := "Zero new scans; fixed rational arithmetic only."
    },
    {
      stepId := "erdos.p13-node148-live-hot-decision"
      stageId? := some "proof-slice.p13-node148-live-hot-decision"
      title := "Exact node [148] live-hot decision"
      plainExplanation := "The runner consumes the identical node-[146] no residual, retains the final recoverable hot aggregate, proves that it pays the hot demand, and uses one corrected total-demand comparison to return exactly node [149] or node [150]."
      formalStatement := "D_{\\rm tot}\\le A_{\\rm skel}+E_{\\rm norm}\\quad\\text{or}\\quad D_{\\rm tot}-A_{\\rm skel}-E_{\\rm norm}\\le D_{\\rm cold}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:cold-window-ledger", title := "Live-hot entropy decision", nodeIds := [148] }
      ]
      declarationGroups := [{
        groupId := "p13-node148-hot-decision"
        title := "Exact predecessor-indexed hot/cold split"
        role := .executionAudit
        explanation := "Both outgoing payloads are indexed by the literal node-[146] no input. Exact hot/cold partition and hot payment turn a failed total cap into a cold shortfall without enumerating any assignment universe."
        declarations := [
          `Erdos64EG.Internal.p13Node148DecisionRefinement,
          `Erdos64EG.Internal.p13Node148_hotDemand_le_allowance,
          `Erdos64EG.Internal.p13Node148_totalDemand_eq_hot_add_cold,
          `Erdos64EG.Internal.p13Node148_totalDemand_le_allowance_add_cold,
          `Erdos64EG.Internal.P13Node148To149,
          `Erdos64EG.Internal.P13Node148To150,
          `Erdos64EG.Internal.p13Node148To150Refinement,
          `Erdos64EG.Internal.p13Node148LocalCheckCount_polynomial,
          `Erdos64EG.Internal.p13Node148WorkBudget_checks
        ]
      }]
      scopeNotes := "This is exactly node [148]. It does not prove node [149]'s asymptotic density conclusion or node [150]'s normalized cold-mass lower bound."
      workBound := "One corrected natural-number comparison, reusing the local packing-order ledger and final recoverable aggregate."
    },
    {
      stepId := "erdos.p13-node149-density-cap"
      stageId? := some "proof-slice.p13-node149-density-cap"
      title := "Original node [149] normalized density cap"
      plainExplanation := "The terminal consumes the identical node-[148] yes residual, retains its node-[146] predecessor index, and divides the corrected finite cap by the positive binary-log budget. The complete natural-number correction is uniformly bounded by an o(n log n) graph-order envelope, so the displayed additive density error tends to zero."
      formalStatement := "\\theta\\le\\theta_{\\rm win}+o(1)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:p13-density", title := "P13 density cap", nodeIds := [149] }
      ]
      declarationGroups := [{
        groupId := "p13-node149-normalized-density"
        title := "Exact predecessor and uniform asymptotic normalization"
        role := .compositionProvenance
        explanation := "The finite cap keeps both scale and skeleton errors. Reusable binary-log lemmas bound literal Nat subtraction, prove the combined graph-order envelope is little-o, and normalize it to one explicit term tending to zero."
        declarations := [
          `Erdos64EG.Internal.verifiedP13Node149DensityCap,
          `Erdos64EG.Internal.VerifiedP13Node149DensityCap.correctedThetaCap,
          `Erdos64EG.Internal.p13Node149ThetaWindow_eq_exact,
          `Erdos64EG.Internal.p13SequentialHotNormalizationError_real_upper,
          `Erdos64EG.Internal.p13SequentialHotNormalizationRealEnvelope_isLittleO,
          `Erdos64EG.Internal.p13Node149ThetaError_tendsto_zero,
          `Erdos64EG.Internal.VerifiedP13Node149DensityCap.theta_le_thetaWindow_add_oOne,
          `Erdos64EG.Internal.VerifiedP13Node149DensityCap.correctedRemainderCap,
          `Erdos64EG.Internal.VerifiedP13Node149DensityCap.localCheckCount_polynomial
        ]
      }]
      scopeNotes := "All six audited node-[149] obligations are proved. This terminal introduces no new branch and performs no graph, state, context, or assignment scan."
      workBound := "Zero new local checks; fixed field normalization of the predecessor's exact natural-number inequality."
    },
    {
      stepId := "erdos.p13-node150-cold-mass"
      stageId? := some "proof-slice.p13-node150-cold-mass"
      title := "Node [150] normalized cold-mass prefix"
      plainExplanation := "The literal node-[148] no residual is retained as an index. Exact manuscript-rate certificates prove both printed threshold coefficients, and the discrete binary-log error is divided by the positive budget to one term tending to zero."
      formalStatement := "C\\ge(\\theta-\\theta_{\\rm win})n-o(n)"
      status := .implemented
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "lem:hot-failure-cold-mass", title := "Hot failure forces cold mass", nodeIds := [150] }
      ]
      declarationGroups := [{
        groupId := "p13-node150-cold-mass"
        title := "Exact predecessor, printed coefficients, and vanishing correction"
        role := .compositionProvenance
        explanation := "Eight of nine obligations are proved. The payload is indexed by the exact node-[148] input, both original decimal bounds use the longer manuscript constant, and the common error tends to zero. Only the upstream surviving-cold exclusions and near-cubic spine state are absent."
        declarations := [
          `Erdos64EG.Internal.p13Node150FiniteColdMass,
          `Erdos64EG.Internal.p13Node150_manuscriptRoute8ColdMassCrossMultiplied,
          `Erdos64EG.Internal.p13Node150_manuscriptNegativeNetColdMassCrossMultiplied,
          `Erdos64EG.Internal.p13ManuscriptRoute8ColdMassCoefficient_printedBracket,
          `Erdos64EG.Internal.p13ManuscriptNegativeNetColdMassCoefficient_printedBracket,
          `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalizationError_real_upper,
          `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalizationRealEnvelope_isLittleO,
          `Erdos64EG.Internal.p13ManuscriptDyadicHotNormalization_div_nlog_tendsto_zero,
          `Erdos64EG.Internal.P13Node150FiniteColdMass,
          `Erdos64EG.Internal.p13Node150LocalCheckCount_polynomial
        ]
      }]
      scopeNotes := "Node [150] remains yellow at 8/9. Its outgoing node-[151] handoff still needs the complete surviving-cold branch exclusions and exact near-cubic spine payload."
      workBound := "Zero new scans; fixed rational arithmetic and reuse of the already computed cold list."
    },
    {
      stepId := "erdos.p13-density-handoff"
      stageId? := some "proof-slice.p13-density-handoff"
      title := "Conditional nodes [22]--[24] exact density branch"
      plainExplanation := "From the exact typed node-[21] output, node [22] compares the fixed-point window and skeleton loads. Node [23] exposes the strict overflow on the literal yes constructor without assuming it is empty. Node [24] retains the complementary no constructor, window cap, packing support, and a reusable theorem converting the later joint high-entropy budget into the sharper cap."
      formalStatement := "118108581006\\,p_{13}\\le1500000000\\,n\\quad\\text{or its strict reverse}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:p13-density", title := "P13 density branch", nodeIds := [22, 23, 24] }
      ]
      declarationGroups := [
        {
          groupId := "p13-density-decision"
          title := "Literal framework decisions and reusable node-[24] transformer"
          role := .compositionProvenance
          explanation := "Core owns both decisions, the strict-leaf closure, the surviving active cursor, and the single accumulated ledger. Node [22] consumes the literal node-[21] ledger output without an application-owned handoff."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode24,
            `Erdos64EG.Internal.node22DensityFamily,
            `Erdos64EG.Internal.Node22High,
            `Erdos64EG.Internal.Node22Low,
            `Erdos64EG.Internal.Node22Stage,
            `Erdos64EG.Internal.node22P13DensityDecision,
            `Erdos64EG.Internal.runInitialThroughNode22,
            `Erdos64EG.Internal.node22LocalChecks_eq_zero,
            `Erdos64EG.Internal.Node23Output,
            `Erdos64EG.Internal.node23StrictWindowOverflow,
            `Erdos64EG.Internal.Node23Stage,
            `Erdos64EG.Internal.node23P13WindowEntropyOverflow,
            `Erdos64EG.Internal.runInitialThroughNode23,
            `Erdos64EG.Internal.Node24HighEntropyJointBudget,
            `Erdos64EG.Internal.Node24HighEntropyCap,
            `Erdos64EG.Internal.node24HighEntropyCap_of_jointBudget,
            `Erdos64EG.Internal.Node24HighEntropyTransformer,
            `Erdos64EG.Internal.node24HighEntropyTransformer,
            `Erdos64EG.Internal.Node24Output,
            `Erdos64EG.Internal.Node24Stage,
            `Erdos64EG.Internal.node24StageEntailsHighEntropyTransformer,
            `Erdos64EG.Internal.node24P13DensityBounds,
            `Erdos64EG.Internal.node24LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageEntails
          ]
        }
      ]
      scopeNotes := "Nodes [22]--[24] remain yellow only because the exact node-[21] producer is still a typed conditional input. Node [23] is an unconditional local continuation of node [22]'s yes constructor; it accepts no quiet-block premise. Node [24]'s local transformer and its StageEntails instance are kernel-checked conditional mathematics, not a node-[52] joint-budget proof."
      workBound := "One proof-level natural-number dichotomy and symbolic arithmetic; no finite universe is scanned."
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
        { label := "lem:p13-actual-attachment-cold-fork", title := "Pointwise actual-attachment cold fork", nodeIds := [153] },
        { label := "rem:p13-actual-attachment-fork-scope", title := "Scope of the actual-attachment fork", nodeIds := [153] }
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
      scopeNotes := "Node [153] is a pointwise actual thirteen-bit adjacency scan. The production same-context adapter maps every exact node-[21] packed window through this cold fork and node [153], and proves that its four structural subledgers partition exactly p13 windows. This auxiliary scan neither constructs nor refutes the weighted live package, and it yields no entropy or density bound."
      workBound := "Worst-case reference budget for one supplied selected window: at most 8192·n assignment/state vector comparisons, each comparing thirteen adjacency bits; equivalently at most 106496·n bit comparisons. The subsequent corridor/path work at node [153] is excluded."
    },
    {
      stepId := "erdos.p13-node21-partxi-route"
      stageId? := some "proof-slice.p13-node21-partxi-route"
      title := "Exact whole-packing route into Part XI"
      plainExplanation := "The production adapter maps the exact CT12 packing list. Each entry retains the node-[21] prefix, classifier-produced thirteen-bit cold residual, identical selected window, and computed node-[153] structural frontier. Filtering by the four honest constructors gives an exact partition of all p13 windows."
      formalStatement := "|P_surplus| + |P_dyadic| + |P_high| + |P_quiet| = p13"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-actual-attachment-cold-fork", title := "Pointwise actual-attachment cold fork", nodeIds := [153] },
        { label := "lem:p13-same-window-structural-frontier", title := "Same-window structural frontier", nodeIds := [153] }
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
      scopeNotes := "This is an exact auxiliary handoff from node [21] into nodes [153]--[153]. It uses thirteen literal adjacency bits, not the 91-row weighted safe/flat package, and it assigns no entropy or density payment to any constructor."
      workBound := "One traversal of the exact packing list plus the already charged fixed thirteen-bit cold fork and node-[153] local work for each supplied window; no additional candidate universe is materialized."
    },
    {
      stepId := "erdos.p13-same-window-structural-frontier"
      stageId? := some "proof-slice.p13-same-window-structural-frontier"
      title := "Same-window P13 structural frontier"
      plainExplanation := "The exact node-[153] cold fork indexes a graph-owned continuation on the same selected window. It returns exactly one of four constructors: a high-degree window position, a dyadic root-cycle hit, the first high-degree corridor vertex with its clean prefix, or a quiet structural germ carrying only an ambient-size support bound."
      formalStatement := "\\mathcal R(P)\\in\\{\\operatorname{surplus}(i),\\operatorname{dyadic}(s,C),\\operatorname{corridorHigh}(s,x),\\operatorname{quiet}(s,\\Gamma)\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-same-window-structural-frontier", title := "Same-window structural frontier", nodeIds := [153] },
        { label := "rem:p13-same-window-frontier-scope", title := "Scope of the same-window frontier", nodeIds := [153] }
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
          explanation := "The result type is indexed by the exact node-[153] cold fork. The thin runner flattens the graph result into precisely the four published constructors and proves their exhaustive disjunction."
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
      scopeNotes := "Node [153] is green only for this pointwise four-way classifier. The window-surplus and corridor-high outputs remain typed open handoffs, and the quiet output is only ColdStructuralGerm, not a constant ColdBoundedGerm. No density, cold-mass, bounded-overlap, or aggregate nodes-[153]–[157] claim follows, and no weighted package is constructed here."
      workBound := "For one supplied selected window, at most 26 + (15·p13 + σW) + n visible local checks: two possible thirteen-position passes, one scan of the existing token schedule, and at most n event checks on the proof-carrying simple return."
    },
    {
      stepId := "erdos.p13-same-window-base-scale-split"
      stageId? := some "proof-slice.p13-same-window-base-scale-split"
      title := "Quiet-germ D1–D3 base-scale split"
      plainExplanation := "When the computed node-[153] result is its quiet constructor, the proof-carrying input retains the exact cold fork, selected window, canonical stub, no-event proof, structural germ, and equality to that run output. One graph-owned comparison at Qbase=4²·13²·2¹³ returns either the literal support bound at most Qbase or the strict long-support inequality."
      formalStatement := "Q_{\\rm base}=4^2 13^2 2^{13},\\qquad |\\operatorname{supp}(\\Gamma)|\\le Q_{\\rm base}\\;\\lor\\;Q_{\\rm base}<|\\operatorname{supp}(\\Gamma)|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-d1d3-base-scale-split", title := "D1–D3 base-scale split", nodeIds := [153] },
        { label := "rem:p13-d1d3-base-scale-scope", title := "Scope of the D1–D3 split", nodeIds := [153] }
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
          explanation := "The scale input cannot be an arbitrary germ: it stores equality with the actual node-[153] quiet output and retains its fork, window, canonical stub, no-event proof, and germ."
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
          explanation := "Node [153] charges only the single natural-number support comparison; construction and scanning of the proof-carrying corridor were already charged at node [153]."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount,
            `Erdos64EG.Internal.p13SameWindowBaseScaleComparisonCount_eq_one
          ]
        }
      ]
      scopeNotes := "Node [153] is only the exact D1–D3 support split on the computed quiet branch. It proves no repetition, D4–D7 semantic completeness, bounded-germ promotion, CT3 compression, weighted package, or density estimate. Its literal short and long residuals feed the separately verified local nodes [153] and [153]."
      workBound := "Exactly one natural-number comparison of the retained support length with the fixed constant Qbase=4²·13²·2¹³. No graph, path, state, response, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-short-third-incidence"
      stageId? := some "proof-slice.p13-same-window-short-third-incidence"
      title := "Short-return third-root incidence"
      plainExplanation := "Equality with node [153]'s computed short constructor fixes the exact bounded deleted-edge return. Minimum degree and the quiet no-high proof make its root cubic. The first return step and restored dart are two distinct incidences, so the declared-order root classifier selects the third and tests only whether that endpoint lies on the supplied return support."
      formalStatement := "x_3\\in\\operatorname{supp}(\\Gamma)\\;\\lor\\;x_3\\notin\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-short-third-incidence", title := "Short-return third incidence", nodeIds := [153] },
        { label := "rem:p13-short-third-incidence-scope", title := "Scope of the short-root split", nodeIds := [153] }
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
          explanation := "The input stores equality with node [153]'s short result. The identical quiet germ supplies root membership and the no-high fact, while the residual supplies the exact Qbase support bound."
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
      scopeNotes := "Node [153] classifies only the third incidence at one computed short-return root. Its two constructors feed the separately verified exact consumers [153] and [153]. It performs no support-wide scan, one-return normalization, boundary response construction, D4–D7 reconstruction, CT3 execution, or density argument."
      workBound := "At most 2·n+3+Qbase visible checks. Only one selected root and its supplied bounded support are inspected; no vertex family, graph family, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-non-root-chord-resolution"
      stageId? := some "proof-slice.p13-same-window-non-root-chord-resolution"
      title := "On-return chord resolution"
      plainExplanation := "Equality with node [153]'s computed on-support constructor locates the selected third endpoint at its canonical support index. The resulting literal chord either has target length and closes through the existing CT1 certificate runner, or its rejection supplies the exact strictly shorter return after the same deleted root edge."
      formalStatement := "x_3\\in\\operatorname{supp}(\\Gamma)\\Longrightarrow\\bigl(C_{2^j}\\subseteq G\\bigr)\\;\\lor\\;|\\Gamma'|<|\\Gamma|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-non-root-chord-resolution", title := "On-return chord resolution", nodeIds := [153] },
        { label := "rem:p13-non-root-chord-resolution-scope", title := "Scope of the chord resolution", nodeIds := [153] }
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
          explanation := "The Erdős input stores equality with node [153]'s computed on-support constructor and passes that same short return to the graph resolver."
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
      scopeNotes := "Node [153] proves exactly the CT1 closure of an accepted local chord and, on the surviving branch, the exact strictly shorter deleted-edge return. That residual feeds the verified one-return normalization [153] and packed-support transition [153]. It does not iterate the return, prove termination, or construct the successor/path semantics still white at [153]."
      workBound := "At most Qbase+1 visible checks: one scan of the supplied short support and one power-of-two length decision. No graph, path, cycle, state, response, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-outside-boundary-star"
      stageId? := some "proof-slice.p13-same-window-outside-boundary-star"
      title := "Outside-return cubic boundary-star ownership"
      plainExplanation := "Equality with node [153]'s computed outside constructor fixes one oriented incidence from the literal return support to its selected third endpoint outside. The already certified cubic root gives a three-leaf star, and cubicity proves those three leaves own every incidence at that root."
      formalStatement := "N_G(r)=\\{x_1,x_2,x_3\\},\\qquad r\\in\\operatorname{supp}(\\Gamma),\\quad x_3\\notin\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-outside-boundary-star", title := "Outside-return cubic boundary star", nodeIds := [153] },
        { label := "rem:p13-outside-boundary-star-scope", title := "Scope of the cubic boundary star", nodeIds := [153] }
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
          explanation := "The Erdős input stores equality with node [153]'s computed outside constructor, so the same short residual, return support, selected incidence, and branch context are retained without accepting an independent nonmembership proof."
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
          explanation := "This node projects proof-carrying node-[153] data; it performs no new primitive scan."
          declarations := [
            `StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar.OutsideRun.additionalChecks_eq_zero,
            `Erdos64EG.Internal.P13SameWindowComputedOutsideBoundary.additionalChecks_eq_zero
          ]
        }
      ]
      scopeNotes := "Node [153] proves only one oriented return-support crossing and exact ownership of the cubic root's three incidences. That residual feeds the verified one-return normalization [153] and packed-support transition [153]. It supplies no all-inside consumer, successor/second stub/path, D4–D7 state, CT3 input, or density estimate."
      workBound := "Zero additional primitive checks beyond node [153]. No support-wide, vertex-family, component, path-family, state, response, or context scan is performed."
    },
    {
      stepId := "erdos.p13-same-window-normalized-return-boundary"
      stageId? := some "proof-slice.p13-same-window-normalized-return-boundary"
      title := "Normalized one-return boundary rejoin"
      plainExplanation := "The exact rejected-chord computation from node [153] and exact outside-boundary computation from node [153] are the only two inputs. The graph normalizer chooses the shorter return and old first step on the chord branch, or the original return and selected third endpoint on the outside branch, while retaining the common cubic root ownership and Qbase bound."
      formalStatement := "|\\Gamma'|\\le |\\Gamma|,\\quad |\\operatorname{supp}(\\Gamma')|\\le Q_{\\rm base},\\quad r x_{\\rm out}\\in E(G),\\quad x_{\\rm out}\\notin\\operatorname{supp}(\\Gamma')"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-normalized-return-boundary", title := "Normalized one-return boundary", nodeIds := [153] },
        { label := "rem:p13-normalized-return-boundary-scope", title := "Scope of the normalized return", nodeIds := [153] }
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
          explanation := "The chord input stores equality with node [153]'s actual runner; the outside input retains node [153]'s exact graph branch. Both are assembled from the same computed node-[153] short residual."
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
      scopeNotes := "Node [153] is only a proof-level one-return normalization. Its exact output feeds verified packed-support transition [153], whose all-inside branch then feeds verified owner-change node [153]. Node [153] itself supplies no owner table or cross-window token, successor/second stub/component path [153], iteration or termination argument, D4–D7 coordinate, CT3 input, or density theorem."
      workBound := "Zero additional primitive checks. The node selects from proof-carrying predecessor data and does not scan a support, vertex set, component family, state family, response family, or context family."
    },
    {
      stepId := "erdos.p13-same-window-packed-support-transition"
      stageId? := some "proof-slice.p13-same-window-packed-support-transition"
      title := "Normalized-return packed-support transition"
      plainExplanation := "Equality with node [153]'s computed normalized result fixes one ambient simple return ending in a selected ambient-cubic window support. A graph-owned ordered edge scan either proves every return-support vertex lies in the union of all ambient-cubic selected-window supports, or returns the first membership transition with its oriented crossing, exact BoundaryStub, outside endpoint, and induced-remainder component."
      formalStatement := "\\operatorname{supp}(\\Gamma')\\subseteq U_{\\rm ac}\\quad\\lor\\quad\\exists\\text{ first }uv:\\quad u\\in U_{\\rm ac},\\quad v\\notin U_{\\rm ac}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-packed-support-transition", title := "Normalized-return packed-support transition", nodeIds := [153] },
        { label := "rem:p13-packed-support-transition-scope", title := "Scope of the packed-support transition", nodeIds := [153] }
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
          title := "Exact node-[153] return provenance"
          role := .compositionProvenance
          explanation := "The Erdős input stores equality with node [153]'s computed result, preserves its Qbase-bounded return as one ambient simple path, and proves its selected-window endpoint belongs to the ambient-cubic support union."
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
      scopeNotes := "The union is over all ambient-cubic selected windows, not the manuscript's selected cold subfamily. Its all-inside branch feeds verified owner-change node [153], while its exact first-transition branch feeds verified component boundary schedule [153]. No aggregate cold mass, iteration, D4–D7 statement, CT3 execution, or density estimate follows."
      workBound := "Exactly 13pn+13p+26pL visible checks, where p is the selected-window packing number and L is the one supplied return length; at most n²+(2Qbase+1)n. No graph, path, coloring, state, response, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-boundary-schedule"
      stageId? := some "proof-slice.p13-same-window-component-boundary-schedule"
      title := "Component boundary schedule and BFS path"
      plainExplanation := "Equality with node [153]'s computed first-transition result fixes the exact boundary stub and returned outside component. The same computed outside BFS finset drives a proof-carrying exit scan, the explicit finite window-slot search, the complete incident-stub schedule, its true cyclic successor, and the declared-order shortest BFS path between the two retained boundary neighbours."
      formalStatement := "s^+(b)\\ne b,\\quad C(s^+(b))=C(b),\\quad P_C(b,s^+(b))\\text{ is a shortest declared-order BFS path}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-boundary-schedule", title := "Component boundary schedule and BFS path", nodeIds := [153] },
        { label := "rem:p13-component-boundary-schedule-scope", title := "Scope of the component boundary schedule", nodeIds := [153] }
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
          title := "Exact node-[153] first-transition provenance"
          role := .compositionProvenance
          explanation := "The thin Erdős adapter retains the actual node-[153] run, exact first-transition stub, outside endpoint, and returned component; it supplies only the inherited nonbridge fact needed for the second return."
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
      scopeNotes := "Node [153] belongs only to node [153]'s short first-transition branch and feeds verified one-state component observation [153]. That branch is incompatible with the verified long node-[153]--[153] branch and its white full-semantic consumer [153]; there is no edge from this short branch to [153] or [153]. Node [153] supplies no D4–D7 label, repetition, Boolean or cold-family semantics, iteration, target closure, CT3 execution, or density estimate."
      workBound := "The visible ledger includes 13p slot checks, L·|C| exit-component lookups, both explicit BFS budgets, |C|² component restriction, token filtering, and the declared-order component BFS; it is at most 50·localScale³."
    },
    {
      stepId := "erdos.p13-same-window-component-d1d3-observation"
      stageId? := some "proof-slice.p13-same-window-component-d1d3-observation"
      title := "One component D1--D3 observation"
      plainExplanation := "This node-[153] support stage consumes its predecessor's exact two-boundary component schedule and independently computes its declared-order BFS-tree shortest path. Equality to that one computed path gives the observation interface's rank; no path family is ordered or scanned. The two literal degrees, two Fin 13 offsets, and connector length form one genuine State (Fin 0), while the empty local response honestly retains MissingD4D7 reconstruction."
      formalStatement := "s_C\\in\\operatorname{State}(\\operatorname{Fin}(0)),\\qquad \\operatorname{MissingD4D7}(s_C)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d1d3-observation", title := "One component D1--D3 observation", nodeIds := [153] },
        { label := "rem:p13-component-d1d3-observation-scope", title := "Scope of the component D1--D3 observation", nodeIds := [153] }
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
          title := "Exact node-[153] schedule and independently computed path"
          role := .compositionProvenance
          explanation := "The adapter consumes node [153]'s actual result and graph input. Its connector is the independently computed declared-order BFS-tree shortest path, and equality with that value is used only to package the existing observation rank."
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
      scopeNotes := "Node [153] constructs one state only. Its MissingD4D7 residual feeds the verified cyclic component D1–D3 ledger split [153], which in turn feeds the white D4–D7 reconstruction/coarse-repeat consumer [153]. Neither edge enters long-branch node [153] or [153]. Node [153] itself proves no state sequence, repetition, D4–D7 reconstruction, CT3 compression, Boolean or cold-family semantics, target closure, or density estimate."
      workBound := "Exactly 2n+13 visible checks and at most 15(n+1). The independently computed BFS path is inherited from node [153]; no path family is generated, ordered, or scanned."
    },
    {
      stepId := "erdos.p13-same-window-component-d1d3-ledger"
      stageId? := some "proof-slice.p13-same-window-component-d1d3-ledger"
      title := "Cyclic component D1--D3 ledger split"
      plainExplanation := "Node [153] requires the exact typed node-[153] residual and retains its state as the anchor row. It traverses node [153]'s complete incident-stub schedule with the stored true cyclic successor and computes one local D1--D3 row per scheduled stub. A finite collision search over only those observed rows returns either two distinct rows with the same coarse state or a proof that the schedule has length at most Qbase."
      formalStatement := "(\\exists i\\ne j,\\ s_i=s_j)\\ \\lor\\ |\\mathcal S_C|\\le Q_{\\rm base}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d1d3-ledger", title := "Cyclic component D1--D3 ledger split", nodeIds := [153] },
        { label := "rem:p13-component-d1d3-ledger-scope", title := "Scope of the cyclic D1--D3 ledger", nodeIds := [153] }
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
          title := "Exact node-[153] anchor and node-[153] schedule"
          role := .compositionProvenance
          explanation := "The source type stores node [153]'s residual and equality to its actual run. The anchor row is projected from that retained value, while every other row is computed from node [153]'s exact complete incident schedule."
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
          explanation := "The thin Erdős adapter runs the observed-row classifier and rewrites the exact state-cardinality bound to Qbase. Both constructors are retained for the still-open node-[153] consumer."
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
      scopeNotes := "Node [153] proves only the local exhaustive split. Its repeated branch records equality of two observed coarse D1--D3 states but does not prove full response equivalence or CT3 removability; its bounded branch proves only schedule length at most Qbase. The D4--D7 reconstruction or coarse-repeat consumer remain an open internal obligation of node [153]. No edge enters long-branch node [153] or [153], and no ambient State universe is enumerated."
      workBound := "At most 100·localScale^4 visible checks over the exact incident schedule and local BFS clauses. The Qbase state-cardinality equality is proof-only."
    },
    {
      stepId := "erdos.p13-same-window-component-d4d7-classifier"
      stageId? := some "proof-slice.p13-same-window-component-d4d7-classifier"
      title := "D4--D7 availability and coarse-repeat routing"
      plainExplanation := "Node [153] consumes the exact node-[153] result. A repeated coarse row pair is passed unchanged to a promoted CT10 refinement; a bounded schedule scans only its stored rows and returns a complete D4--D7 family or its first typed missing row, which is also routed through CT10 on the actual branch context."
      formalStatement := "\\text{node-[153] result}\\Longrightarrow\\text{routed coarse repeat, reconstructed rows, or routed first missing row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d4d7-classifier", title := "D4--D7 availability and coarse-repeat classifier", nodeIds := [153] },
        { label := "rem:p13-component-d4d7-classifier-scope", title := "Scope of the D4--D7 classifier", nodeIds := [153] }
      ]
      declarationGroups := [{
        groupId := "p13-component-d4d7-classifier-total"
        title := "Exact node-174 consumer, two CT10 routes, and local work"
        role := .semanticTheorem
        explanation := "The graph runner consumes only node [153]'s observed split. Both generic CT10 routes preserve the actual context and promote an explicit retained row; the thin P13 adapter proves generic and specialized predecessor equality and the combined local work bound."
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
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.coarseHandoffContract,
          `StructuralExhaustion.Routes.InducedPathComponentD4D7ToCT10.missingHandoffContract
        ]
      }]
      scopeNotes := "Node [153] classifies only the availability of graph-derived D4--D7 clauses and retains exact refinement residuals. It proves no full D4--D7 compatible-response equivalence, CT8 removal, certified smaller object, second connector, cycle, or target closure; those implications remain an open internal obligation of node [153]."
      workBound := "At most 3·localScale primitive checks over the actual incident schedule and two retained CT10 inputs. The State, response, context, graph, and universe families are never enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-d4d7-semantics"
      stageId? := some "proof-slice.p13-same-window-component-d4d7-readiness"
      title := "Component D4--D7 semantic readiness"
      plainExplanation := "This node-[153] support stage consumes its predecessor's exact execution. The complete-reconstruction constructor is impossible at the retained anchor row; the surviving coarse and bounded constructors preserve their CT10 objects and explicit missing D4--D7 witnesses."
      formalStatement := "\\text{node-[153] execution}\\Longrightarrow\\text{coarse missing pair or bounded first-missing row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-component-d4d7-semantic-readiness", title := "Component D4--D7 semantic readiness", nodeIds := [153] }
      ]
      declarationGroups := [{
        groupId := "p13-component-d4d7-readiness-total"
        title := "Exact node-[153] residual and local constructor elimination"
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
      scopeNotes := "Node [153] proves readiness only. It does not construct compatible-response equivalence, a remove operation, a smaller object, or CT8 execution; those remain an open internal obligation of node [153]."
      workBound := "One predecessor-constructor inspection, bounded by localScale+1. No response, context, state, graph, or universe family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-component-ct8-consumer"
      stageId? := some "proof-slice.p13-component-d4d7-clause-schedule"
      title := "Fixed D4--D7 clause schedule"
      plainExplanation := "Node [153] retains every exact node-[153] missing marker and assigns only the fixed noduplicated D4,D5,D6,D7 obligation order. It deliberately asserts no clause truth."
      formalStatement := "\\text{node-[153] marker}\\Longrightarrow[D4,D5,D6,D7]\\text{ obligation ledger}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4d7-clause-schedule", title := "Fixed D4--D7 clause schedule", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-d4d7-clause-schedule-total"
        title := "Exact markers, fixed schedule, and actual emitted-slot bound"
        role := .semanticTheorem
        explanation := "The graph layer constructs a four-slot ledger from each retained marker. The application proves exact node-[153] equality, exhaustiveness, and that the computed output emits eight slots on the coarse branch or four on the bounded branch."
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
      scopeNotes := "Node [153] schedules obligations only. It proves no clause predicate, response equivalence, removal, smaller object, or CT8 execution; those remain an open internal obligation of node [153]."
      workBound := "At most eight actual emitted slots; ambient universes are not inspected."
    },
    {
      stepId := "erdos.p13-component-d4d7-semantic-consumer"
      stageId? := some "proof-slice.p13-component-d4d7-clause-cursor"
      title := "D4 obligation cursor"
      plainExplanation := "This node-[153] support stage consumes its predecessor's exact ledgers, focuses D4 as the next obligation, and retains D5--D7 as an exact unevaluated tail."
      formalStatement := "[D4,D5,D6,D7]\\Longrightarrow D4\\ \\text{ focused with tail }[D5,D6,D7]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4d7-clause-cursor", title := "D4 obligation cursor", nodeIds := [153] }]
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
      scopeNotes := "Node [153] asserts no D4 truth or response/CT8 semantics; those remain an open internal obligation of node [153]."
      workBound := "At most six retained tail slots."
    },
    {
      stepId := "erdos.p13-component-d4d7-d4-consumer"
      stageId? := some "proof-slice.p13-component-d4-local-clause-request"
      title := "Graph-derived D4 evaluation request"
      plainExplanation := "Node [153] preserves node [153]'s exact dependent cursor and emits a singleton request for the actual D4 head while retaining D5--D7 unchanged."
      formalStatement := "D4::[D5,D6,D7]\\Longrightarrow\\text{request }[D4]\\text{ with tail }[D5,D6,D7]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-local-clause-request", title := "Local D4 evaluation request", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-d4-local-request"
        title := "Exact dependent D4 requests"
        role := .semanticTheorem
        explanation := "The framework request stores only the actual cursor, singleton D4 slot, and exact tail. The application proves exact node-[153] provenance, exhaustiveness, and two actual requests on the coarse branch or one on the bounded branch."
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
      scopeNotes := "Node [153] supplies no predicate, truth value, response equivalence, or CT8 result; graph-derived semantics remain an open internal obligation of node [153]."
      workBound := "At most two actual singleton request slots; no ambient universe is enumerated."
    },
    {
      stepId := "erdos.p13-component-d4-semantics"
      stageId? := some "proof-slice.p13-component-d4-evaluator-residual"
      title := "D4 evaluator residual"
      plainExplanation := "Node [153] preserves every exact node [153] request and exposes the missing graph-local predicate and provenance requirements without accepting an evaluator."
      formalStatement := "\\text{D4 request}\\Longrightarrow[\\text{graph-local predicate},\\text{provenance}]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-evaluator-residual", title := "D4 evaluator residual", nodeIds := [153] }]
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
      scopeNotes := "No Boolean, predicate, evaluator, response equivalence, or CT8 result is supplied; node [153] records the terminal construction residual."
      workBound := "At most four actual requirement tags."
    },
    {
      stepId := "erdos.p13-component-d4-evaluator-producer"
      stageId? := some "proof-slice.p13-component-d4-evaluator-construction-residual"
      title := "Graph-owned D4 evaluator construction residual"
      plainExplanation := "Node [153] preserves every exact node-[153] request, marker, and D5--D7 tail and records the three graph-owned inputs still needed to construct the D4 evaluator."
      formalStatement := "\\text{node-[153] residual}\\Longrightarrow[\\text{component data},\\text{predicate definition},\\text{derivation}]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-evaluator-construction-residual", title := "D4 evaluator construction residual", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-d4-evaluator-construction-residual"
        title := "Exact graph-owned construction requirements"
        role := .semanticTheorem
        explanation := "The graph layer retains node [153] exactly and appends only the ordered construction tags; the application proves the coarse and bounded leaves exhaustively."
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
      stepId := "erdos.p13-component-d4-evaluation"
      stageId? := some "proof-slice.p13-component-d4-evaluation"
      title := "Graph-owned D4 evaluation after node [153]"
      plainExplanation := "Without adding a numbered diagram node, the exact node-[153] marker determines the component path and its local D4 coordinate family. The evaluator computes omegaTwo on actual attachment labels and retains the literal D5,D6,D7 tail."
      formalStatement := "\\text{node-[153] marker}\\Longrightarrow\\text{exact local D4 response with tail }[D5,D6,D7]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-component-d4-evaluator", title := "Graph-owned D4 evaluation after node [153]", nodeIds := [153] }]
      declarationGroups := [
        {
          groupId := "p13-component-d4-local-family"
          title := "Fixed graph-owned D4 coordinate family"
          role := .frameworkInterface
          explanation := "Coordinates use only the two retained boundary-window roles and internal wedges of the one stored component-path support; the response is the literal omegaTwo predicate on graph-derived attachment labels."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD4.activeSupport,
            `StructuralExhaustion.Graph.InducedPathComponentD4.coordinates,
            `StructuralExhaustion.Graph.InducedPathComponentD4.response_true_iff,
            `StructuralExhaustion.Graph.InducedPathComponentD4.semantics,
            `StructuralExhaustion.Graph.InducedPathComponentD4.state_localResponse
          ]
        },
        {
          groupId := "p13-component-d4-exact-execution"
          title := "Exact post-frontier execution"
          role := .semanticTheorem
          explanation := "The graph evaluator retains the node-[153] residual definitionally, proves response provenance, and preserves D5--D7. The Erdős adapter returns two exact evaluations on the coarse branch and one on the bounded branch."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.run,
            `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.Evaluation.semantics_and_response_provenance,
            `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.Evaluation.tail_preserved,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.exact_node191,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_exhaustive
          ]
        },
        {
          groupId := "p13-component-d4-local-work"
          title := "Local cubic work bound"
          role := .workBound
          explanation := "One marker costs at most four times the cube of the ambient vertex count: two adjacency decisions classify each raw triple and at most two boundary-role responses evaluate each retained wedge. The exact coarse and bounded constructors therefore cost at most 8n^3 and 4n^3 respectively."
          declarations := [
            `StructuralExhaustion.Graph.InducedPathComponentD4.visibleChecks_le_cubic,
            `StructuralExhaustion.Graph.InducedPathComponentD4Evaluator.visibleChecks_polynomial,
            `Erdos64EG.Internal.P13SameWindowFirstTransitionBoundaryInput.runD4Evaluation_localWork
          ]
        }
      ]
      scopeNotes := "This support stage belongs to original node [153]. This stage proves D4 only: D5, D6, Boolean D7 semantics, compatible-response equality, removal, a smaller object, and CT8 remain open."
      workBound := "At most 8n^3 checks on the coarse leaf and 4n^3 on the bounded leaf, including raw-wedge classification and boundary-role response evaluation; no ambient response, context, state, graph, or universe family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-packed-owner-change"
      stageId? := some "proof-slice.p13-same-window-packed-owner-change"
      title := "Ambient-cubic owner sequence and first cross-window edge"
      plainExplanation := "Equality with node [153]'s all-inside result fixes the same normalized return. A once-prepared finite inventory assigns and stores the unique ambient-cubic selected-window owner of every return vertex. The single-window result contradicts the original external stub neighbour, so the surviving result is the first owner-change edge with two exact opposite cross-window tokens."
      formalStatement := "\\exists i<|\\Gamma'|:\\quad W_i\\ne W_{i+1}\\quad\\text{and two exact cross-window tokens}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-packed-owner-change", title := "First ambient-cubic owner change", nodeIds := [153] },
        { label := "rem:p13-packed-owner-change-scope", title := "Scope of the owner change", nodeIds := [153] }
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
          explanation := "The input stores equality with node [153]'s computed all-inside constructor and passes that same Qbase-bounded path and containment proof into the generic owner preparation."
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
      scopeNotes := "Owners range over all ambient-cubic selected windows, not the manuscript cold subfamily. Its exact first-cross-window package feeds verified zero-check handoff node [153]. Node [153] constructs no boundary successor, target-cycle closure, cold aggregate, D4–D7 coordinate, CT3 input, or density estimate."
      workBound := "At most n²+Qbase(n+1) visible checks using one prepared slot inventory, one stored owner lookup per path vertex, and one stored-owner comparison per edge."
    },
    {
      stepId := "erdos.p13-same-window-cross-window-token-pair"
      stageId? := some "proof-slice.p13-same-window-cross-window-token-pair"
      title := "Exact cross-window token-pair residual"
      plainExplanation := "This node-[153] support stage consumes its predecessor's complete first-cross-window package. A reusable typed route projects the two already computed endpoint tokens, proves they are distinct opposite oriented contributions of the same literal edge, and retains both exact cross-window subtypes without performing another search. This is the terminal residual of the computed all-inside branch."
      formalStatement := "t_L\\ne t_R\\quad\\land\\quad \\operatorname{subtype}(t_L)=\\operatorname{subtype}(t_R)=\\mathtt{crossWindow}\\quad\\land\\quad e(t_L)=e(t_R)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-cross-window-token-pair", title := "Exact cross-window token-pair residual", nodeIds := [153] },
        { label := "rem:p13-cross-window-token-pair-scope", title := "Scope of the token-pair residual", nodeIds := [153] }
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
          explanation := "The input is the complete computed node-[153] first-cross-window residual, including its stored table, first hit, crossing, and exact run equality."
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
          explanation := "All fields are proof-carrying projections from node [153]; the residual adds no primitive predicate evaluation."
          declarations := [
            `Erdos64EG.Internal.p13SameWindowCrossWindowTokenPair_additionalChecks_eq_zero
          ]
        }
      ]
      scopeNotes := "Node [153] is the exact terminal residual of the computed all-inside branch. It proves no second connector, repeated-owner structure, cycle, cold-family membership, demand or capacity bound, successor, target closure, CT execution, or density estimate."
      workBound := "Exactly zero additional primitive checks after node [153]; no graph, path, connector, cycle, state, demand, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-support-prefix"
      stageId? := some "proof-slice.p13-same-window-long-support-prefix"
      title := "Exact long-support forced prefix"
      plainExplanation := "Equality with node [153]'s computed long constructor retains Qbase below the literal support length on the identical branch context. The generic handoff embeds the first Qbase+1 positions, identifies Qbase as the unique overflow index, and classifies any supplied support position as inside that prefix or after it."
      formalStatement := "Q_{\\rm base}<|\\operatorname{supp}(\\Gamma)|\\Longrightarrow\\{0,\\ldots,Q_{\\rm base}\\}\\hookrightarrow\\operatorname{supp}(\\Gamma)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-support-prefix", title := "Forced long-support prefix", nodeIds := [153] },
        { label := "rem:p13-long-support-prefix-scope", title := "Scope of the long prefix", nodeIds := [153] }
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
            `StructuralExhaustion.Routes.LongFiniteSupportHandoff.handoff
          ]
        },
        {
          groupId := "p13-long-prefix-provenance"
          title := "Exact computed-long source"
          role := .compositionProvenance
          explanation := "The input stores equality with node [153]'s long result. The thin source and result retain the literal corridor length, exact Qbase scale, strict inequality, and identical ambient graph."
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
      scopeNotes := "Node [153] provides only literal finite positions and exact inclusions. It assigns no normalized state labels and supplies no D4–D7 response, CT17 target/offset/compatibility semantics, or density estimate. Its exact prefix feeds verified first-nine classifier [153]."
      workBound := "Zero scans to construct the forced prefix; one natural-number comparison for each supplied position classification. No support family, state universe, graph family, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-state-labels"
      stageId? := some "proof-slice.p13-same-window-long-prefix-state-labels"
      title := "First-nine coarse-label collision and CT10 refinement"
      plainExplanation := "This node-[153] support stage consumes its predecessor's actual run, maps only its first nine exact positions to the literal corridor, computes the graph-derived degree-modulo-four and selected-packing-membership label, retains a collision in the eight-label alphabet, and promotes the missing compatible-response layer through CT10."
      formalStatement := "\\exists i\\ne j<9,\\ (d_G(v_i)\\bmod 4,\\mathbf 1_{v_i\\in V(\\mathcal P_{13})})=(d_G(v_j)\\bmod 4,\\mathbf 1_{v_j\\in V(\\mathcal P_{13})})"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-prefix-observed-label", title := "First-nine observed-label refinement", nodeIds := [153] },
        { label := "rem:p13-long-prefix-observed-label-scope", title := "Scope of first-nine refinement", nodeIds := [153] }
      ]
      declarationGroups := [{
        groupId := "p13-long-prefix-observed-label-total"
        title := "Exact local collision, route, CT10 trace, and work"
        role := .semanticTheorem
        explanation := "The graph layer scans only nine actual occurrences; the route preserves node [153]'s exact source and gives CT10 precisely the two collided positions. The exhaustive trace promotes responseContexts, while the work ledger remains linear in the local graph size."
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
      scopeNotes := "Node [153] proves only equality of one graph-derived coarse label at two distinct literal first-nine occurrences. Node [153] refines their full degrees; D4–D7 response equivalence, CT8 removal, and a certified smaller object remain an open internal obligation of node [153]."
      workBound := "At most 144(|V|+1)+9 primitive checks: the fixed first-nine collision scan plus the three-class CT10 scan on two retained occurrences. No ambient label, response, context, state, graph, or universe family is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-full-semantics"
      stageId? := some "proof-slice.p13-same-window-long-prefix-degree-refinement"
      title := "Two-occurrence exact degree refinement"
      plainExplanation := "Node [153] retains node [153]'s actual collided pair and promoted CT10 response-context obligation, reads only the two literal corridor degree rows, and returns equal full degrees or a nonzero degree gap with the already proved common residue modulo four."
      formalStatement := "d_G(v_i)=d_G(v_j)\\quad\\lor\\quad d_G(v_i)\\ne d_G(v_j)\\ \\wedge\\ d_G(v_i)\\equiv d_G(v_j)\\pmod 4"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:p13-long-prefix-degree-refinement", title := "Two-occurrence exact degree refinement", nodeIds := [153] }
      ]
      declarationGroups := [{
        groupId := "p13-long-prefix-degree-total"
        title := "Exact collision provenance and two local degree rows"
        role := .semanticTheorem
        explanation := "The source re-exposes the exact node-[153] result, promoted CT10 response-context field, and literal vertices. The classifier compares their full degrees and preserves distinctness, packing-bit equality, and residue equality in both branches."
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
      scopeNotes := "Node [153] proves only exact degree refinement. It does not construct D4--D7 responses, response equivalence, CT8 removal, or a smaller object; those remain an open internal obligation of node [153]."
      workBound := "Exactly 2|V|+1 visible local degree checks, at most 2(|V|+1). No response, context, state, graph, or universe enumeration."
    },
    {
      stepId := "erdos.p13-same-window-long-prefix-response-consumer"
      stageId? := some "proof-slice.p13-long-prefix-local-clause-alignment"
      title := "First-nine local-clause alignment"
      plainExplanation := "Node [153] retains the exact node-[153] degree branch and CT10 obligation, then compares adjacency of its two literal vertices on exactly the same nine prefix coordinates."
      formalStatement := "(\\exists\\text{ first mismatch below }9)\\ \\lor\\ (\\forall i<9,\\ A(v,i)=A(w,i))"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-local-clause-alignment", title := "First-nine local-clause alignment", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-long-prefix-local-alignment-total"
        title := "Exact node-[153] source and nine local adjacency clauses"
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
      scopeNotes := "Node [153] proves alignment on nine clauses only, not D4--D7 response equivalence or CT8 removal; those remain an open internal obligation of node [153]."
      workBound := "Exactly 18 local adjacency evaluations. No ambient response, context, state, graph, or universe enumeration."
    },
    {
      stepId := "erdos.p13-long-prefix-full-response-consumer"
      stageId? := some "proof-slice.p13-long-prefix-extended-clause-alignment"
      title := "First-eighteen local-clause alignment"
      plainExplanation := "Node [153] passes through an inherited mismatch or scans only literal positions 9--17 after first-nine alignment, yielding a second mismatch or first-eighteen alignment."
      formalStatement := "\\text{mismatch below 18}\\ \\lor\\ \\forall i<18,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-extended-clause-alignment", title := "First-eighteen local-clause alignment", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-extended-local-alignment"
        title := "Exact second-block scan"
        role := .semanticTheorem
        explanation := "The runner retains nested node-[153]/CT10 provenance and scans exactly the second nine literal coordinates."
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
      scopeNotes := "Node [153] proves first-eighteen adjacency alignment only, not full response equivalence or CT8; those remain an open internal obligation of node [153]."
      workBound := "At most 18 new adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-response-semantics"
      stageId? := some "proof-slice.p13-long-prefix-third-block-clause-alignment"
      title := "First-twenty-seven local-clause alignment"
      plainExplanation := "Node [153] passes through either inherited mismatch unchanged or scans only literal positions 18--26 after first-eighteen alignment."
      formalStatement := "\\text{mismatch below 27}\\ \\lor\\ \\forall i<27,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-third-block-clause-alignment", title := "First-twenty-seven local-clause alignment", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-third-block-local-alignment"
        title := "Exact third-block scan"
        role := .semanticTheorem
        explanation := "The runner preserves node-[153], degree, and CT10 provenance; earlier mismatches pass through and only the third nine-coordinate block is newly scanned."
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
      scopeNotes := "Node [153] proves only first-twenty-seven adjacency alignment, not response equivalence or CT8; those remain an open internal obligation of node [153]."
      workBound := "At most 18 new local adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-full-semantics"
      stageId? := some "proof-slice.p13-long-prefix-fourth-block-clause-alignment"
      title := "First-thirty-six local-clause alignment"
      plainExplanation := "Node [153] passes through all earlier mismatch leaves and otherwise scans only literal positions 27--35."
      formalStatement := "\\text{mismatch below 36}\\ \\lor\\ \\forall i<36,\\ A(v,i)=A(w,i)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-fourth-block-clause-alignment", title := "First-thirty-six local-clause alignment", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-fourth-block-local-alignment"
        title := "Exact fourth-block scan"
        role := .semanticTheorem
        explanation := "The exact node-[153] result, degree residual, and CT10 obligation are retained; only the fourth nine-coordinate block is newly scanned."
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
      scopeNotes := "Node [153] proves only first-thirty-six adjacency alignment; node [153] records the terminal response/CT8 residual."
      workBound := "At most 18 new local adjacency evaluations."
    },
    {
      stepId := "erdos.p13-long-prefix-response-producer"
      stageId? := some "proof-slice.p13-long-prefix-compatible-response-frontier"
      title := "Long-prefix compatible-response frontier"
      plainExplanation := "Node [153] retains all five node-[153] leaves and their degree and CT10 provenance. A local consumer turns every fixed-block mismatch into a proved distinguishing adjacency response with exact first-hit and offset provenance. The fully aligned leaf retains its four alignment proofs and exposes only the complete D4--D7 response semantics and exact-pair certified reduction still needed for CT8."
      formalStatement := "\\text{node-[153] leaf}\\Longrightarrow\\text{distinguishing fixed response}\\;\\lor\\;\\text{aligned CT8 requirement}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:p13-long-prefix-compatible-response-frontier", title := "Compatible-response frontier", nodeIds := [153] }]
      declarationGroups := [{
        groupId := "p13-long-prefix-compatible-response-frontier"
        title := "Exact five-leaf residual frontier"
        role := .semanticTheorem
        explanation := "The graph layer retains the exact predecessor, maps the four first-hit mismatch constructors to literal response contexts at offsets 0, 9, 18, and 27, and keeps the aligned constructor as a two-producer CT8 requirement. The application retains node [153], degree provenance, and the CT10 response-context tag."
        declarations := [
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_exhaustive,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.run_predecessor,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.requiredInputs_le_three,
          `StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier.visibleChecks_constant,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.responseContexts_card,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.ofFirstMismatch,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.ofSecondMismatch,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.ofThirdMismatch,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.ofFourthMismatch,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.exactType,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.resolve,
          `StructuralExhaustion.Graph.LongPrefixCT8Response.alignedReservedChecks_polynomial,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.exact_node192,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_degree_result,
          `Erdos64EG.Internal.P13SameWindowLongPrefixCompatibleResponseFrontierSource.retained_ct10_responseContexts,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_requiredInputs,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_visibleChecks,
          `Erdos64EG.Internal.runP13SameWindowLongPrefixCompatibleResponseFrontier_ambient_preserved,
          `Erdos64EG.Internal.resolveP13SameWindowLongPrefixCompatibleResponseFrontier,
          `Erdos64EG.Internal.resolveP13SameWindowLongPrefixCompatibleResponseFrontier_exhaustive,
          `Erdos64EG.Internal.p13SameWindowLongPrefixResponseVisibleChecks_eq,
          `Erdos64EG.Internal.p13SameWindowLongPrefixResponseVisibleChecks_polynomial
        ]
      }]
      scopeNotes := "The four mismatch leaves now have genuine local distinguishing contexts. Equality on the 36 displayed adjacency clauses is still not complete D4--D7 response equivalence, and no unrelated smaller object is accepted; the aligned leaf remains open for those exact two producers."
      workBound := "One retained-constructor inspection. Mismatch inequalities reuse the preceding fixed-block scans. The 73-operation aligned CT8 budget is recorded only as prospective work and is not executed until its two missing producers exist; no ambient response, prefix, vertex-subset, graph, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-same-window-dyadic-terminal"
      stageId? := some "proof-slice.p13-same-window-dyadic-terminal"
      title := "Computed dyadic frontier constructor closes"
      plainExplanation := "When the computed node-[153] result is its dyadic constructor, the adapter uses that constructor's canonical stub position and restored root cycle—without accepting another witness—to build the exact cold dyadic hit. The existing one-check CT1 G1 runner reaches C1, contradicting the inherited target-avoidance field."
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
          explanation := "The branch object records equality with the computed node-[153] dyadic constructor. Its cold hit has exactly the same window, stub offset, first-hit payload, and restored root-cycle walk."
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
          explanation := "The thin node-[153] consumer exposes the exact C1 terminal, typed trace, one-check count, and final contradiction."
          declarations := [
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1Run,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_terminal,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_trace,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.g1_checks,
            `Erdos64EG.Internal.P13ComputedDyadicBranch.impossible
          ]
        }
      ]
      scopeNotes := "Node [155] is green only as the consumer of node [153]'s computed dyadic constructor. This does not construct a bounded germ, close the surplus or quiet constructors, or validate the separate aggregate G1 producer claimed after nodes [153]–[154]."
      workBound := "One supplied-certificate CT1 check after the already accounted node-[153] scan; no cycle, walk, graph, or context family is enumerated."
    },
    {
      stepId := "erdos.p13-node25-large-remainder"
      stageId? := some "proof-slice.p13-node25-large-remainder"
      title := "Exact Residual A at node [25]"
      plainExplanation := "The literal node-[24] active cursor determines the canonical packing complement. The framework maps that cursor once and records the exact partition, scaled large-remainder inequality, and hereditary induced-P13-freeness."
      formalStatement := "R=V(G)\\setminus\\bigcup\\mathcal P,\\qquad 98608581006\\,n\\le118108581006\\,|R|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:p13-density", title := "Residual A", nodeIds := [25] }
      ]
      declarationGroups := [{
        groupId := "p13-node25-exact-remainder"
        title := "Literal node-[24] successor and canonical complement"
        role := .compositionProvenance
        explanation := "The application proves only node [25]'s remainder facts; Core transports every prior branch and ledger fact."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode25,
          `Erdos64EG.Internal.Node25Remainder,
          `Erdos64EG.Internal.Node25Output,
          `Erdos64EG.Internal.Node25Stage,
          `Erdos64EG.Internal.node25P13LargeRemainder,
          `Erdos64EG.Internal.node25LocalChecks_eq_zero,
          `StructuralExhaustion.Core.DensityAsymptoticTransport.nat_partition_complement_lower,
          `Erdos64EG.Internal.p13Remainder_partition,
          `Erdos64EG.Internal.p13Remainder_free,
          `Erdos64EG.Internal.p13Remainder_componentwise_free
        ]
      }]
      scopeNotes := "Node [25] is locally kernel-checked but partial because its exact predecessor chain contains missing node-[21] and node-[23] producers."
      workBound := "Zero new graph scans; symbolic arithmetic over the already selected packing."
    },
    {
      stepId := "erdos.p13-node26-remainder-continuation"
      stageId? := some "proof-slice.p13-node26-remainder-continuation"
      title := "Residual A panel continuation at node [26]"
      plainExplanation := "Node [26] consumes the literal node-[25] output and names exactly the same canonical remainder for Part II."
      formalStatement := "R_{26}=R_{25}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "fig:proof-diagram-part-ii", title := "Residual A continuation", nodeIds := [26] }
      ]
      declarationGroups := [{
        groupId := "p13-node26-continuation"
        title := "Framework-owned zero-copy successor"
        role := .compositionProvenance
        explanation := "The output contains only the definitional remainder identity; predecessor and ledger transport remain in Core."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode26,
          `Erdos64EG.Internal.Node26Output,
          `Erdos64EG.Internal.Node26Stage,
          `Erdos64EG.Internal.node26P13RemainderContinuation,
          `Erdos64EG.Internal.node26LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
        ]
      }]
      scopeNotes := "Node [26] is locally proved but remains partial through inherited missing predecessors."
      workBound := "Zero local checks."
    },
    {
      stepId := "erdos.p13-node27-no-three-core"
      stageId? := some "proof-slice.p13-node27-no-three-core"
      title := "No internal three-core at node [27]"
      plainExplanation := "The exact node-[26] remainder satisfies both the induced-support and finite-internal-subgraph formulations of the paper's no-three-core conclusion."
      formalStatement := "R\\text{ has no internal subgraph of minimum degree at least }3"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "fig:proof-diagram-part-ii", title := "No internal three-core", nodeIds := [27] }
      ]
      declarationGroups := [{
        groupId := "p13-node27-core-exclusion"
        title := "Exact remainder core exclusion"
        role := .semanticTheorem
        explanation := "The framework mapper consumes the literal node-[26] cursor and applies the two existing graph lemmas on that same remainder."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode27,
          `Erdos64EG.Internal.Node27Output,
          `Erdos64EG.Internal.Node27Stage,
          `Erdos64EG.Internal.node27P13NoInternalThreeCore,
          `Erdos64EG.Internal.node27LocalChecks_eq_zero,
          `Erdos64EG.Internal.p13Remainder_internalThreeCore_free,
          `Erdos64EG.Internal.p13Remainder_internalSubgraphThreeCore_free
        ]
      }]
      scopeNotes := "Node [27] is locally proved but remains partial through inherited missing predecessors."
      workBound := "Zero new graph, subgraph, or support scans."
    },
    {
      stepId := "erdos.p13-positive-deficiency"
      stageId? := some "proof-slice.p13-positive-deficiency"
      title := "Positive deficiency of the exact P13 remainder"
      plainExplanation := "Node [28] maps the literal node-[27] cursor and records the graph-owned positive-deficiency sum on the same exact remainder."
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
          `Erdos64EG.Internal.runInitialThroughNode28,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.internalDegree,
          `StructuralExhaustion.Graph.AssignedSupportCharge.Profile.positiveDeficiency,
          `Erdos64EG.Internal.p13RemainderDeficiencyProfile,
          `Erdos64EG.Internal.p13Remainder_positiveDeficiency_eq,
          `Erdos64EG.Internal.Node28Output,
          `Erdos64EG.Internal.Node28Stage,
          `Erdos64EG.Internal.node28P13PositiveDeficiency,
          `Erdos64EG.Internal.node28LocalChecks_eq_zero
        ]
      }]
      scopeNotes := "The local node-[28] theorem is kernel-checked, but the node remains partial through its predecessor chain's missing obligations."
      workBound := "Zero new ambient-support or subgraph enumeration."
    },
    {
      stepId := "erdos.p13-external-incidence-supply"
      stageId? := some "proof-slice.p13-external-incidence-supply"
      title := "External-incidence supply on the exact remainder"
      plainExplanation := "The exact node-[28] positive deficiency is charged vertex by vertex to actual edges leaving R. Every R--W edge appears in the selected-window token schedule, whose exact cardinality is 15p₁₃+σ_W. Subtracting the same remainder surplus gives the second inequality, while the bounded node-[21] certificate supplies the paper's near-cubic error term."
      formalStatement := "\\operatorname{def}^{+}(R)\\le e(R,W)\\le15p_{13}+\\sigma_W,\\qquad \\operatorname{def}^{+}(R)-\\sigma_R\\le15p_{13}+\\sigma_W-\\sigma_R"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:stub-positive", title := "External-incidence supply", nodeIds := [29] },
        { label := "lem:surplus-aware-window-stub", title := "Exact surplus-aware stub bound", nodeIds := [29] }
      ]
      declarationGroups := [{
        groupId := "p13-node29-exact-incidence-ledger"
        title := "Exact predecessor, incidence accounting, and spine bound"
        role := .semanticTheorem
        explanation := "The framework mapper consumes the literal node-[28] value. Graph lemmas own the boundary injection, token embedding, exact token identity, surplus partition, and local work bound; the bounded-surplus fact is used directly from the incoming branch proof."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode29,
          `Erdos64EG.Internal.Node29Output,
          `Erdos64EG.Internal.Node29Stage,
          `Erdos64EG.Internal.node29P13ExternalIncidenceSupply,
          `Erdos64EG.Internal.node29LocalChecks_eq_zero,
          `Erdos64EG.Internal.p13Curvature_positiveDeficiency_eq_previous,
          `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.positiveDeficiency_le_boundaryIncidences,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_tokenCount,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.tokenCount_eq_fifteen_mul_packing_add_surplus,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_fifteen_mul_packing_add_surplus,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_sub_remainderSurplus_le,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.window_add_remainder_eq_totalSurplus,
          `StructuralExhaustion.Graph.InducedPathWindowLedger.checks_le_thirteen_mul_square,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
        ]
      }]
      scopeNotes := "The local node-[29] accounting is kernel-checked, but the node remains partial through inherited missing obligations. It proves no wedge or rank conclusion."
      workBound := "At most 13n² checks: scan the thirteen positions of each already selected window against the declared ambient vertex schedule. No path, packing, support, subgraph, graph, Boolean-state, or context universe is enumerated."
    },
    {
      stepId := "erdos.p13-wedge-lower"
      stageId? := some "proof-slice.p13-wedge-lower"
      title := "Exact wedge lower bound on the remainder"
      plainExplanation := "The graph-owned degree count is applied to every supplied component and to the exact remainder. Node [29]'s incidence supply yields the finite window error and the exact printed window-rate lower bound."
      formalStatement := "W_2(C)\\ge3|V(C)|-2\\operatorname{def}^{+}(C),\\qquad W_2(R)\\ge(3-2\\tau)|R|-2\\varepsilon"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:wedge-lower", title := "Wedge lower bound", nodeIds := [30] }
      ]
      declarationGroups := [{
        groupId := "p13-node30-exact-wedge-lower"
        title := "Exact predecessor, degree count, and rate transport"
        role := .semanticTheorem
        explanation := "The framework mapper consumes the literal node-[29] value. The graph-owned wedge identity proves component and aggregate floors, and the application performs only the fixed window-rate arithmetic."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode30,
          `Erdos64EG.Internal.Node30Output,
          `Erdos64EG.Internal.Node30Stage,
          `Erdos64EG.Internal.node30P13WedgeLower,
          `Erdos64EG.Internal.node30LocalChecks_eq_zero,
          `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.three_mul_card_le_wedgeCount_add_twice_deficiency,
          `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeFloor,
          `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeRate_of_deficiencyRate,
          `Erdos64EG.Internal.p13Remainder_wedgeFloor,
          `Erdos64EG.Internal.p13Node30OmegaWindow,
          `Erdos64EG.Internal.p13Node30OmegaWindow_gt_printed,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
        ]
      }]
      scopeNotes := "The local node-[30] theorem is kernel-checked, but the node remains partial through inherited missing obligations. It constructs no curvature-rank object."
      workBound := "One induced-neighbour scan for each remainder vertex, bounded by n². The rate transports are arithmetic consequences and enumerate no components, supports, paths, quotients, contexts, subgraphs, graphs, or state universes."
    },
    {
      stepId := "erdos.p13-curvature-target-rank"
      stageId? := some "proof-slice.p13-curvature-target-rank"
      title := "Curvature target-rank on the exact wedge family"
      plainExplanation := "The raw coordinate family consists exactly of a remainder center and a canonical unordered pair of its internal neighbours, so its cardinality is W₂(R). The public rank is now the attained maximum over every carrier-indexed functional admissible quotient of the exact graph response profile."
      formalStatement := "r_\\Omega(R)=\\max\\{|\\mathcal A|:\\mathcal A\\subseteq\\mathcal W_2(R),\\ \\mathcal A\\text{ survives every functional admissible quotient}\\}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:curvature-target-rank", title := "Curvature target-rank", nodeIds := [31] }
      ]
      declarationGroups := [{
        groupId := "p13-node31-certified-quotient-rank"
        title := "Literal wedge coordinates and attained certified-candidate maximum"
        role := .mathematicalDefinition
        explanation := "The framework mapper consumes node [30] exactly. FunctionalAdmissibleRank owns the carrier-indexed maximum; the Erdős layer supplies only the literal wedge schedule, graph response profile, and coordinate-count bridges."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode31,
          `Erdos64EG.Internal.Node31Output,
          `Erdos64EG.Internal.Node31Stage,
          `Erdos64EG.Internal.node31P13CurvatureTargetRank,
          `Erdos64EG.Internal.node31LocalChecks_eq_zero,
          `Erdos64EG.Internal.p13CurvatureCoordinates,
          `Erdos64EG.Internal.p13CurvatureCoordinates_card_eq_wedgeCount,
          `Erdos64EG.Internal.p13CurvatureCoordinates_card_le_cube,
          `Erdos64EG.Internal.p13CurvatureResponseProfile,
          `Erdos64EG.Internal.p13CurvatureFunctionalRankProfile,
          `Erdos64EG.Internal.p13CurvatureTargetRank,
          `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.targetRank_le_coordinates,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoYesClosedActive
        ]
      }]
      scopeNotes := "The local node-[31] rank construction is kernel-checked, but the node remains partial through inherited missing obligations."
      workBound := "The explicit coordinate schedule contains exactly W₂(R) and at most n³ actual wedges. The maximum is a proof-level bounded cardinality definition: no subfamily powerset, quotient family, outside-context family, support family, path family, subgraph family, or graph universe is evaluated."
    },
    {
      stepId := "erdos.p13-curvature-rank-decision"
      stageId? := some "proof-slice.p13-curvature-rank-decision"
      title := "Exact near-full-rank decision"
      plainExplanation := "Node [32] executes CT15's exact decision on node [31]'s rank profile. The framework returns either literal strict loss against the declared wedge-coordinate cardinality, or equality with that full cardinality."
      formalStatement := "r_\\Omega(R)<W_2(R)\\quad\\lor\\quad r_\\Omega(R)=W_2(R)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:target-rank-circuit", title := "Rank-loss decision and circuit input", nodeIds := [32] }
      ]
      declarationGroups := [{
        groupId := "p13-node32-exact-rank-decision"
        title := "Exact predecessor and exhaustive two-edge rank split"
        role := .semanticTheorem
        explanation := "CT15 owns the strict-loss/full-cardinality constructors and exhaustive rank decision; Core owns the two residual branches and preservation of the accumulated ledger."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode32,
          `Erdos64EG.Internal.node32RankDecision,
          `Erdos64EG.Internal.Node32RankDrop,
          `Erdos64EG.Internal.Node32FullRank,
          `Erdos64EG.Internal.Node32Stage,
          `Erdos64EG.Internal.node32P13RankDropDecision,
          `Erdos64EG.Internal.node32LocalChecks_eq_zero,
          `Erdos64EG.Internal.node32RankDecision_exhaustive,
          `Erdos64EG.Internal.node32RankDecisionWork_eq_zero,
          `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision,
          `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision_exhaustive,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoNoAfterYes
        ]
      }]
      scopeNotes := "The local decision is kernel-checked but remains partial through inherited missing predecessors. The two paper edges are retained exactly."
      workBound := "Zero executable scans after node [31]. The decision compares a proof-level maximum with its declared cardinality and evaluates no coordinate subfamily, quotient, outside context, support, path, subgraph, graph, or state universe."
    },
    {
      stepId := "erdos.p13-curvature-dependence-open"
      stageId? := some "proof-slice.p13-curvature-dependence-open"
      title := "Node-[33] rank-reducing branch marker"
      plainExplanation := "Node [33] consumes only node [32]'s strict-loss constructor and attaches PUnit as the existing cross-panel marker. Circuit extraction is deliberately left to node [35]."
      formalStatement := "[32]_{\\rm strict}\\longrightarrow[33]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:target-rank-circuit", title := "Target-rank circuit extraction", nodeIds := [33] }
      ]
      declarationGroups := [{
        groupId := "p13-node33-branch-marker"
        title := "Framework-owned strict-loss continuation"
        role := .compositionProvenance
        explanation := "The decision proof remains in node [32]; this node performs no pair-circuit or support construction."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode33,
          `Erdos64EG.Internal.Node33Output,
          `Erdos64EG.Internal.Node33Stage,
          `Erdos64EG.Internal.node33P13RankReducingBranch,
          `Erdos64EG.Internal.node33LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionYes
        ]
      }]
      scopeNotes := "The local marker is kernel-checked but remains partial through inherited missing predecessors."
      workBound := "Zero local checks."
    },
    {
      stepId := "erdos.p13-full-curvature-rank"
      stageId? := some "proof-slice.p13-full-curvature-rank"
      title := "Node-[34] full-rank branch marker"
      plainExplanation := "Node [34] consumes only node [32]'s threshold-reaching constructor and attaches PUnit as the separate cross-panel marker. The exact branch proposition remains in node [32]'s stage."
      formalStatement := "[32]_{\\rm full}\\longrightarrow[34]"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:full-rank", title := "Forcing of full admissible quotient-rank", nodeIds := [34] }
      ]
      declarationGroups := [{
        groupId := "p13-node34-branch-marker"
        title := "Framework-owned threshold-reaching continuation"
        role := .compositionProvenance
        explanation := "No rank equality or maximal family is copied into node [34]; node [47] later continues the literal branch."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode34,
          `Erdos64EG.Internal.Node34Output,
          `Erdos64EG.Internal.Node34Stage,
          `Erdos64EG.Internal.node34P13FullRankResidual,
          `Erdos64EG.Internal.node34LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueActiveCursorDecisionNo
        ]
      }]
      scopeNotes := "The local marker is kernel-checked but remains partial through inherited missing predecessors."
      workBound := "Zero local checks."
    },
    {
      stepId := "erdos.remainder-curvature-rank"
      stageId? := some "proof-slice.p13-curvature-rank"
      title := "Node-[35] functional pair circuit"
      plainExplanation := "Node [35] consumes node [33]'s marker and node [32]'s retained rank-loss proof, extracts CT15's canonical proof-carrying pair circuit, and projects its exact support-stratified determination certificate."
      formalStatement := "r_\\Omega(R)<W_2(R)\\Longrightarrow\\exists a\\ne b,\\ q(a)=q(b)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:target-rank-circuit", title := "Rank-dependence routing", nodeIds := [35] }
      ]
      declarationGroups := [
        {
          groupId := "remainder-curvature-ct15"
          title := "Framework-owned circuit extraction"
          role := .compositionProvenance
          explanation := "Core maps only the strict branch. CT15 supplies the pair circuit and its support-stratified certificate; the candidate's exactness fields prevent substitution of another quotient, coordinate pair, or carrier."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode35,
            `Erdos64EG.Internal.Node35PairCircuit,
            `Erdos64EG.Internal.Node35CollisionSupportCertificate,
            `Erdos64EG.Internal.node35RankDropOnDeclaredCoordinates,
            `Erdos64EG.Internal.node35PairCircuit,
            `Erdos64EG.Internal.node35CollisionSupportCertificate,
            `Erdos64EG.Internal.Node35Output,
            `Erdos64EG.Internal.Node35Stage,
            `Erdos64EG.Internal.node35P13RankCircuit,
            `Erdos64EG.Internal.node35LocalChecks_eq_zero,
            `StructuralExhaustion.CT15.CertifiedDeterminationRank.Profile.pairCircuitOfRankDrop,
            `StructuralExhaustion.CT15.SupportStratifiedRank.Profile.certificate,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
          ]
        }
      ]
      scopeNotes := "Node [35]'s local responsibility is unconditional: its certificate is owned by the CT15 candidate and its predecessor and sibling transport are framework-owned."
      workBound := "Zero executable scans. The framework retrieves and transports the exact predecessor payload; it enumerates no quotient, context, support, subgraph, graph, or ambient state universe."
    },
    {
      stepId := "erdos.p13-curvature-context-validity"
      stageId? := some "proof-slice.p13-curvature-context-validity"
      title := "Original-atom context validity audit"
      plainExplanation := "Node [35]'s candidate is target-complete at its final carrier, while node [36] asks a separate question at the original atom. The framework keeps those dependent context types distinct and makes the exact mismatch-or-universal decision only over the original atom interface."
      formalStatement := "\\bigl(\\exists K_C,\\ \\rho_C(a,K_C)\\ne\\rho_C(b,K_C)\\bigr)\\ \\lor\\ \\bigl(\\forall K_C,\\ \\rho_C(a,K_C)=\\rho_C(b,K_C)\\bigr)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:curvature-dependence-routing", title := "Outside-context validity decision", nodeIds := [36] }
      ]
      declarationGroups := [{
        groupId := "p13-node36-context-validity"
        title := "Exact predecessor and framework-owned two-edge context decision"
        role := .semanticTheorem
        explanation := "The framework decides only node [35]'s active cursor. The two predicates are read from the certificate's original-interface audit and never identify atom contexts with carrier contexts."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode36,
          `Erdos64EG.Internal.Node36OriginalUniversal,
          `Erdos64EG.Internal.Node36OriginalDefect,
          `Erdos64EG.Internal.node36OriginalUniversalDecidable,
          `Erdos64EG.Internal.node36OriginalDefectOfNotUniversal,
          `Erdos64EG.Internal.node35ActiveCursorFamily,
          `Erdos64EG.Internal.Node36Stage,
          `Erdos64EG.Internal.node36P13OriginalContextAudit,
          `Erdos64EG.Internal.node36LocalChecks_eq_zero,
          `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.OriginalContextAudit,
          `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.auditOriginal,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuation
        ]
      }]
      scopeNotes := "The local decision is kernel-checked but remains yellow through node [35]'s typed support input and earlier conditional predecessors."
      workBound := "Zero executable checks. Contexts occur only under proof-level quantifiers; no context, coordinate, quotient, support, path, subgraph, graph, or state family is generated."
    },
    p13Node37ProofStep,
    p13Node38ProofStep,
    p13Node39ProofStep,
    {
      stepId := "erdos.p13-curvature-enlarged-support"
      stageId? := some "proof-slice.p13-curvature-enlarged-support"
      title := "Strict enlarged-support payload"
      plainExplanation := "Node [40] focuses node [38]'s strict-enlargement constructor. The connectedness, support, determination, and minimality facts remain in node [35]'s single accumulated certificate."
      formalStatement := "C\\subsetneq X,\\quad X\\text{ connected and inclusion-minimal for }a\\mapsto b"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:curvature-dependence-routing", title := "Enlarged connected support route", nodeIds := [40] }
      ]
      declarationGroups := [{
        groupId := "p13-node40-enlarged-support"
        title := "Exact strict-support constructor"
        role := .semanticTheorem
        explanation := "Core focuses the final no leaf without an application-owned output or route."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode40,
          `Erdos64EG.Internal.Node40Stage,
          `Erdos64EG.Internal.node40P13EnlargedConnectedSupport,
          `Erdos64EG.Internal.node40LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.focusActiveCursorYesContinuationFinalNo
        ]
      }]
      scopeNotes := "The local focus is kernel-checked but remains yellow through the conditional node-[35] support certificate."
      workBound := "Zero scans: all support and determination fields are projections from the selected certificate."
    },
    {
      stepId := "erdos.p13-curvature-carrier-scope"
      stageId? := some "proof-slice.p13-curvature-carrier-scope"
      title := "Proper-or-whole carrier scope"
      plainExplanation := "Node [41] reads the proper/whole tag of node [40]'s exact carrier and uses Core's focused-branch decision to retain exactly the two paper edges."
      formalStatement := "X\\text{ proper}\\quad\\lor\\quad X=G"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:proper-smearing", title := "Proper/whole support classification", nodeIds := [41] }
      ]
      declarationGroups := [{
        groupId := "p13-node41-carrier-scope"
        title := "Framework-owned focused carrier decision"
        role := .compositionProvenance
        explanation := "Core retains the opaque bypass and exact active leaf on both constructors; the application supplies only the stored carrier predicates."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode41,
          `Erdos64EG.Internal.Node41Bypass,
          `Erdos64EG.Internal.Node41Active,
          `Erdos64EG.Internal.Node41Proper,
          `Erdos64EG.Internal.Node41Whole,
          `Erdos64EG.Internal.Node41Stage,
          `Erdos64EG.Internal.node41P13CarrierScopeDecision,
          `Erdos64EG.Internal.node41LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranch
        ]
      }]
      scopeNotes := "The local decision is kernel-checked but remains partial through inherited missing obligations."
      workBound := "Zero checks and no graph or support scan."
    },
    {
      stepId := "erdos.p13-curvature-proper-carrier-terminal"
      stageId? := some "proof-slice.p13-curvature-proper-carrier-terminal"
      title := "Proper enlarged-carrier CT3 terminal"
      plainExplanation := "On node [41]'s proper constructor, the admitted functional quotient is injective by the graph-owned proper-carrier theorem, contradicting node [35]'s distinct equal-code pair."
      formalStatement := "X\\subsetneq G\\wedge\\operatorname{Representative}(X)\\Longrightarrow\\bot"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:proper-smearing", title := "Proper delocalization supports are forbidden", nodeIds := [42] }
      ]
      declarationGroups := [{
        groupId := "p13-node42-proper-ct3"
        title := "Graph-owned proper-carrier injectivity terminal"
        role := .semanticTheorem
        explanation := "Core closes only the proper leaf; the application supplies one graph theorem and no branch plumbing."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode42,
          `Erdos64EG.Internal.Node42Stage,
          `Erdos64EG.Internal.node42ProperSupportImpossible,
          `Erdos64EG.Internal.node42P13ProperSupportSmearingClosure,
          `Erdos64EG.Internal.node42LocalChecks_eq_zero,
          `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_originalEligible,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
        ]
      }]
      scopeNotes := "The local closure is kernel-checked but remains partial through inherited missing obligations. The whole constructor bypasses node [42]."
      workBound := "One stored CT3 theorem application; no finite search."
    },
    {
      stepId := "erdos.p13-curvature-whole-carrier"
      stageId? := some "proof-slice.p13-curvature-whole-carrier"
      title := "Whole-carrier exact handoff"
      plainExplanation := "Node [43] consumes node [41]'s whole constructor directly and transports it along the stored equality between the admitted candidate carrier and the determination certificate carrier."
      formalStatement := "X=G"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:no-silent-global-smearing", title := "Whole-graph delocalization barrier", nodeIds := [43] }
      ]
      declarationGroups := [{
        groupId := "p13-node43-whole-handoff"
        title := "Framework-owned whole-leaf continuation"
        role := .compositionProvenance
        explanation := "Core continues only the no leaf. The sole new payload is whole-ness of the exact determination carrier."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode43,
          `Erdos64EG.Internal.Node43Output,
          `Erdos64EG.Internal.Node43Stage,
          `Erdos64EG.Internal.node43P13WholeGraphDelocalization,
          `Erdos64EG.Internal.node43LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
        ]
      }]
      scopeNotes := "The local continuation is kernel-checked but remains partial through inherited missing obligations."
      workBound := "Zero checks."
    },
    {
      stepId := "erdos.p13-curvature-repair-identity"
      stageId? := some "proof-slice.p13-curvature-repair-identity"
      title := "One--three repair identity"
      plainExplanation := "Node [44] retains node [43] exactly and derives the manuscript's component identity from the handshake and connected cycle-rank equations."
      formalStatement := "s=p-2+2\\beta_Z-\\sigma_Z"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:smearing-support-repair", title := "One--three repair identity", nodeIds := [44] }
      ]
      declarationGroups := [{
        groupId := "p13-node44-repair-identity"
        title := "Framework integer identity and graph specialization"
        role := .semanticTheorem
        explanation := "The framework mapper consumes node [43]'s exact output and the graph layer proves the identity on one supplied component."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode44,
          `Erdos64EG.Internal.Node44Output,
          `Erdos64EG.Internal.Node44Stage,
          `Erdos64EG.Internal.node44P13RepairIdentity,
          `Erdos64EG.Internal.node44LocalChecks_eq_zero,
          `StructuralExhaustion.Core.OneThreeRepair.identity,
          `StructuralExhaustion.Graph.OneThreeRepair.Component.identity,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
        ]
      }]
      scopeNotes := "The local identity is kernel-checked but remains partial through inherited missing obligations; injectivity belongs to node [45]."
      workBound := "Symbolic integer arithmetic only."
    },
    {
      stepId := "erdos.p13-curvature-closed-exact-barrier"
      stageId? := some "proof-slice.p13-curvature-closed-exact-barrier"
      title := "Whole-carrier exact-label barrier"
      plainExplanation := "Node [45] applies the graph-owned whole-carrier theorem to the already admitted functional quotient and obtains injectivity of its raw code."
      formalStatement := "X=G\\Longrightarrow\\operatorname{Inj}(q)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:no-silent-global-smearing", title := "Whole-graph delocalization barrier", nodeIds := [45] }
      ]
      declarationGroups := [{
        groupId := "p13-node45-exact-barrier"
        title := "Graph-owned whole-carrier injectivity"
        role := .semanticTheorem
        explanation := "The framework mapper consumes node [44]'s exact output; the graph theorem proves injectivity directly from admission and the stored whole tag."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode45,
          `Erdos64EG.Internal.Node45Output,
          `Erdos64EG.Internal.Node45Stage,
          `Erdos64EG.Internal.node45P13GlobalProfileBarrier,
          `Erdos64EG.Internal.node45LocalChecks_eq_zero,
          `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_whole,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
        ]
      }]
      scopeNotes := "The local injectivity theorem is kernel-checked but remains partial through inherited missing obligations; node [46] applies it."
      workBound := "Proof selection for one hypothetical collision; no quotient, context, coordinate, or support family is evaluated."
    },
    {
      stepId := "erdos.p13-curvature-rank-drop-terminal"
      stageId? := some "proof-slice.p13-curvature-rank-drop-terminal"
      title := "Whole-carrier rank-drop contradiction"
      plainExplanation := "Node [46] applies node [45]'s injectivity to the two distinct coordinates that node [35] retained with equal quotient values."
      formalStatement := "a\\ne b\\wedge q(a)=q(b)\\wedge\\operatorname{Inj}(q)\\Longrightarrow\\bot"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:full-rank", title := "Rank-drop closure", nodeIds := [46] }
      ]
      declarationGroups := [{
        groupId := "p13-node46-rank-drop-terminal"
        title := "Exact collision contradiction"
        role := .semanticTheorem
        explanation := "The node-local theorem combines node [45]'s injectivity with the literal distinct-coordinate identification, and Core closes exactly the focused whole-carrier leaf."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode46,
          `Erdos64EG.Internal.Node46Stage,
          `Erdos64EG.Internal.node46WholeRankDropImpossible,
          `Erdos64EG.Internal.node46P13RankDropClosure,
          `Erdos64EG.Internal.node46LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeFocusedBranchNoContinuation
        ]
      }]
      scopeNotes := "Node [46] closes only the whole-carrier rank-drop edge. Its local theorem is kernel-checked but the run remains partial through missing node-[21] and node-[35] producers."
      workBound := "One theorem application and zero executable checks."
    },
    {
      stepId := "erdos.p13-curvature-full-rank-cross-panel"
      stageId? := some "proof-slice.p13-curvature-full-rank-cross-panel"
      title := "Exact node-[47] full-rank handoff"
      plainExplanation := "Node [47] is the separate continuation of node [34]'s full-rank constructor. It retains that exact predecessor, equality rΩ(R)=W₂(R), and an attained maximal family; it does not consume any rank-drop terminal."
      formalStatement := "[34]\\Longrightarrow[47]:\\quad r_\\Omega(R)=W_2(R)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:full-rank", title := "Full-rank join", nodeIds := [47] }
      ]
      declarationGroups := [{
        groupId := "p13-node47-full-rank-handoff"
        title := "Independent exact full-rank continuation"
        role := .compositionProvenance
        explanation := "The accumulated ledger retains node [34]. Node [47] is definitionally that same stage, and the framework retrieves it without an application-owned copy or handoff."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode47,
          `Erdos64EG.Internal.Node47Stage,
          `Erdos64EG.Internal.node47P13FullRankContinuation,
          `Erdos64EG.Internal.node47LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
        ]
      }]
      scopeNotes := "Node [47] is the complementary node-[34] edge and is not downstream of node [46] or node [37]. Its local continuation is kernel-checked but the complete run remains partial through inherited missing obligations."
      workBound := "Zero scans and one exact predecessor handoff."
    },
    {
      stepId := "erdos.forced-curvature-cost-split"
      stageId? := some "proof-slice.p13-forced-curvature-cost-split"
      title := "Forced curvature cost"
      plainExplanation := "The literal node-[47] value produces node [48] on the full accumulated residual. Core arithmetic transports combine its inherited density and wedge ledgers, divide by the positive exact certificate scale, and multiply by cOmega=log2(543958/111286). For fixed manuscript thresholds the resulting cost error is o(|R|)."
      formalStatement := "c_\\Omega r_\\Omega(R)\\ge K_{\\rm win}|R|-o(|R|),\\qquad c_\\Omega=\\log_2(543958/111286)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "cor:forced-curvature-cost", title := "Forced curvature cost", nodeIds := [48] },
        { label := "rem:curvature-provenance", title := "Curvature-cost provenance", nodeIds := [48] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node48-support"
          title := "Exact finite curvature cost"
          role := .compositionProvenance
          explanation := "The node-[48] successor consumes the exact node-[47] stage from the accumulated ledger. During migration, one certificate indexed by that literal leaf supplies the two finite accounting inequalities; Lean derives the two cost-unit conclusions and Core owns every bypass and branch transport."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode48,
            `Erdos64EG.Internal.node48CurvatureEntropyCost,
            `Erdos64EG.Internal.node48WindowCurvatureDensity,
            `Erdos64EG.Internal.node48HighEntropyCurvatureDensity,
            `Erdos64EG.Internal.node48WindowForcedCost,
            `Erdos64EG.Internal.node48HighEntropyForcedCost,
            `Erdos64EG.Internal.node48CostError,
            `Erdos64EG.Internal.Node48Output,
            `Erdos64EG.Internal.Node48Stage,
            `Erdos64EG.Internal.node48P13ForcedCurvatureCost,
            `Erdos64EG.Internal.node48LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
          ]
        }
      ]
      scopeNotes := "Node [48] owns the two finite accounting inequalities and their two paper-local forced-cost transports. Only the finite inequalities remain explicitly conditional on the exact leaf-indexed migration input; the cost transports are kernel-checked and the input is not cited as proved evidence. Construction of the remainder state family belongs to node [49]."
      workBound := "Zero local scans; no graph family, context universe, subset family, assignment cube, or Boolean universe is generated."
    },
    {
      stepId := "erdos.finite-remainder-state-entropy"
      stageId? := some "proof-slice.p13-finite-remainder-entropy"
      title := "Per-vertex remainder entropy"
      plainExplanation := "Node [49] follows the original definition literally: on the fixed carrier V(R), it forms the subtype of labelled simple graphs satisfying the inherited atom-subcubic, induced-P13-free, no-internal-3-core, and current net-deficiency-cap predicates, and takes its symbolic finite cardinality."
      formalStatement := "\\mathcal G(R)=\\{H\\text{ on }V(R):H\\text{ satisfies the four remainder constraints}\\},\\qquad \\eta(R)=\\frac{\\log_2|\\mathcal G(R)|}{|R|}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:remainder-entropy", title := "Per-vertex skeleton entropy of the remainder", nodeIds := [49] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node49-constrained-family"
          title := "Framework-owned constrained graph family"
          role := .mathematicalDefinition
          explanation := "Graph owns the predicate-defined finite graph subtype. Erdős supplies only the four manuscript predicates on the fixed remainder and the exact symbolic entropy identity, while Core maps the accumulated active cursor."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode49,
            `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.State,
            `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.stateCount,
            `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.normalizedEntropy,
            `StructuralExhaustion.Graph.ConstrainedLabelledGraphFamily.Profile.normalizedEntropy_eq,
            `Erdos64EG.Internal.node49RemainderGraphAdmissible,
            `Erdos64EG.Internal.node49RemainderGraphFamilyProfile,
            `Erdos64EG.Internal.node49RemainderGraphFamilyCount,
            `Erdos64EG.Internal.node49RemainderEntropy,
            `Erdos64EG.Internal.Node49Output,
            `Erdos64EG.Internal.Node49Output.entropyExact,
            `Erdos64EG.Internal.Node49Stage,
            `Erdos64EG.Internal.node49P13RemainderEntropy,
            `Erdos64EG.Internal.node49LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionNoContinuation
          ]
        }
      ]
      scopeNotes := "This node only defines the constrained family and eta(R). The high/low threshold split and all consequences belong to node [50] and later nodes. The older realized conditional-fibre entropy declarations remain reusable support but are not evidence for node [49]."
      workBound := "Zero executable semantic checks: finiteness is inherited symbolically from the finite labelled-graph carrier, and no graph, subgraph, context, assignment, or Boolean universe is enumerated."
    },
    {
      stepId := "erdos.entropy-scale-split"
      stageId? := some "proof-slice.p13-entropy-scale-split"
      title := "Exact manuscript entropy split"
      plainExplanation := "Node [50] consumes node [49]'s exact eta(R), retains the complete dependent predecessor, and applies the framework's generic ordered-threshold dichotomy to the literal real inequality printed in the original diagram."
      formalStatement := "\\eta(R)\\ge\\frac1{10}\\log_2 n\\quad\\lor\\quad\\eta(R)<\\frac1{10}\\log_2 n"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:remainder-entropy", title := "Per-vertex remainder entropy threshold", nodeIds := [50] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node50-ordered-threshold"
          title := "Framework-owned ordered entropy threshold"
          role := .compositionProvenance
          explanation := "Core owns the exhaustive ordered split and zero-work ledger. The Erdős layer supplies only eta(R), the printed threshold, and the exact node-[49] predecessor."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode50,
            `StructuralExhaustion.Core.OrderThresholdSplit.Profile.exhaustive,
            `Erdos64EG.Internal.Node50Bypass,
            `Erdos64EG.Internal.Node50Active,
            `Erdos64EG.Internal.node50EntropyThreshold,
            `Erdos64EG.Internal.node50EntropyProfile,
            `Erdos64EG.Internal.Node50High,
            `Erdos64EG.Internal.Node50Low,
            `Erdos64EG.Internal.Node50Stage,
            `Erdos64EG.Internal.node50P13EntropyDecision,
            `Erdos64EG.Internal.node50_exhaustive,
            `Erdos64EG.Internal.node50LocalChecks_eq_zero,
            `Erdos64EG.Internal.node50ThresholdWork_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorDecisionNoContinuation
          ]
        }
      ]
      scopeNotes := "Node [50] proves only the exhaustive high/low entropy split. Node [51] must consume the high constructor, while node [53] and the later low-entropy analysis must consume the low constructor; those consumers are separate obligations."
      workBound := "Zero primitive checks. The split is logical and keeps both real expressions symbolic; no logarithm, graph family, state family, subset family, context universe, function space, assignment cube, or Boolean universe is evaluated."
    },
    {
      stepId := "erdos.high-remainder-bits"
      stageId? := some "proof-slice.p13-high-remainder-bits"
      title := "High-entropy remainder bit contribution"
      plainExplanation := "Node [51] consumes the exact high-edge proposition of the manuscript node-[50] entropy split on the full accumulated residual. Node [49]'s eta(R)=log2|G(R)|/|R| identity then gives the printed remainder-bit contribution by symbolic real arithmetic."
      formalStatement := "\\eta(R)\\ge\\frac1{10}\\log_2 n\\Longrightarrow (|R|/10)\\log_2 n\\le\\log_2|\\mathcal G(R)|"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:high-remainder-bits", title := "High-power remainder bit contribution", nodeIds := [51] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node51-high-bits"
          title := "Exact node-50 high-entropy transfer"
          role := .compositionProvenance
          explanation := "The framework retains the literal node-[50] decision and its high-edge proof in the accumulated ledger. The Erdős layer adds only the manuscript bit inequality, using node-[49]'s registered entropy identity."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode51,
            `Erdos64EG.Internal.Node51Output,
            `Erdos64EG.Internal.node51Output,
            `Erdos64EG.Internal.Node51Stage,
            `Erdos64EG.Internal.node51P13HighEntropyBranch,
            `Erdos64EG.Internal.node51LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
          ]
        }
      ]
      scopeNotes := "Node [51] is only the high-branch arithmetic handoff. It feeds the original node-[52] window-plus-remainder accounting step; it does not prove window/remainder independence or the downstream entropy cap."
      workBound := "No new finite scan and no real-number search. The proof reuses the zero-check node-[50] ordered split and node-[49]'s symbolic entropy identity; it evaluates no graph family, state universe, context universe, assignment cube, or Boolean universe."
    },
    {
      stepId := "erdos.window-remainder-framework-handoff"
      stageId? := some "proof-slice.p13-window-remainder-accounting"
      title := "Accumulated node-[52] framework handoff"
      plainExplanation := "The framework maps only node [51]'s exact high continuation, retains every sibling unchanged, and retrieves node [24]'s transformer from the single accumulated ledger. During migration the previously verified same-context joint budget is accepted only through a certificate indexed by that literal leaf."
      formalStatement := "\\text{high}_{51}\\longrightarrow\\left[\\frac{1-13\\theta}{10}+118.108581006\\,\\theta\\le1.5+o(1)\\right]"
      status := .implemented
      correspondence := .supporting
      manuscriptRefs := [
        { label := "prop:two-budget", title := "Two-budget routing", nodeIds := [52] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node52-accumulated-handoff"
          title := "Branch-preserving local feasibility handoff"
          role := .compositionProvenance
          explanation := "Core owns exact predecessor retention, low-edge pass-through, and the reusable query into node [24]. The Erdős layer conditionally installs only the paper's same-context joint budget and the theta cap entailed by that retrieved transformer."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode52,
            `Erdos64EG.Internal.Node52Output,
            `Erdos64EG.Internal.node52InheritedQuery,
            `Erdos64EG.Internal.Node52Stage,
            `Erdos64EG.Internal.node52P13WindowRemainderAccounting,
            `Erdos64EG.Internal.node52LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.LedgerQuery.entailedStage,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuationDerived
          ]
        }
      ]
      scopeNotes := "The framework transition and inherited node-[24] implication are kernel-checked. The same-context joint-budget producer is missing and is not cited as proved evidence."
      workBound := "Zero semantic checks and no graph, context, state-product, assignment-cube, or Boolean-universe enumeration."
    },
    {
      stepId := "erdos.window-remainder-density-accounting"
      title := "Window-plus-remainder accounting"
      plainExplanation := "The original node [52] must add node [51]'s remainder bits to the inherited independently target-testable multiscale window contribution, compare the resulting local bit total with the near-cubic skeleton budget, and solve the resulting scalar inequality."
      formalStatement := "\\frac{1-13\\theta}{10}+118.108581006\\,\\theta\\le1.5+o(1)\\Longrightarrow\\theta\\le0.01198542083\\ldots+o(1)"
      status := .next
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:two-budget", title := "Two-budget routing", nodeIds := [52] },
        { label := "prop:p13-density", title := "Near-cubic P13 window density bounds", nodeIds := [52] }
      ]
      scopeNotes := "Framework routing and the exact finite target proposition are implemented. The missing producer is the paper's local addition of the inherited window and remainder bit contributions against their common skeleton budget."
      workBound := "Pure symbolic arithmetic over inherited ledger facts, with zero ambient graph, context, state-product, assignment-cube, or Boolean-universe enumeration."
    },
    {
      stepId := "erdos.node54-entropy-cap-closure"
      stageId? := some "proof-slice.p13-entropy-cap-closure"
      title := "Two-edge node-[54] entropy-cap closure"
      plainExplanation := "Node [54] handles exactly its two incoming paper edges. The node-[52] output rules out the strict reverse of its stored joint budget; on node [53]'s strict-small edge, the same order contradiction uses a capacity certificate indexed by that literal low leaf."
      formalStatement := "A\\le B\\Longrightarrow\\neg(B<A)"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:entropy-high-theta", title := "Entropy cap closes the high-theta branch", nodeIds := [54] }
      ]
      declarationGroups := [{
        groupId := "p13-node54-high-theta-terminal"
        title := "Framework-owned two-edge terminal"
        role := .compositionProvenance
        explanation := "Core terminalizes node [52]'s high leaf, closes node [53]'s nested yes leaf, and focuses only the nested no leaf. The typed migration input supplies solely the old small-edge capacity theorem at its exact indices."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode54,
          `Erdos64EG.Internal.Node54HighTheta,
          `Erdos64EG.Internal.Node54HighOutput,
          `Erdos64EG.Internal.node54HighOutput,
          `Erdos64EG.Internal.Node54SmallCapacity,
          `Erdos64EG.Internal.node54SmallBudgetImpossible,
          `Erdos64EG.Internal.Node54Bypass,
          `Erdos64EG.Internal.Node54Active,
          `Erdos64EG.Internal.Node54Stage,
          `Erdos64EG.Internal.node54P13EntropyCapClosure,
          `Erdos64EG.Internal.node54LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
        ]
      }]
      scopeNotes := "Both local contradiction lemmas and their framework composition are kernel-checked. The stage remains partial through inherited missing obligations and the missing node-[53]-small capacity producer."
      workBound := "Zero executable checks: two symbolic order contradictions, with no graph, context, state, product, assignment, or Boolean-universe scan."
    },
    {
      stepId := "erdos.low-entropy-forced-cost-fit"
      stageId? := some "proof-slice.p13-low-entropy-forced-cost-fit"
      title := "Accumulated node-[53] budget decision"
      plainExplanation := "Node [53] consumes only node [50]'s exact low constructor. It compares the exact remaining labelled-skeleton bits after the hot-window and node-[49] remainder demands with the inherited full-rank curvature cost, retaining both manuscript edges. The high constructor and node [51] output pass through unchanged."
      formalStatement := "B_{\\rm skel}-B_{\\rm win}-B_R<K_{\\Omega}\\quad\\text{or}\\quad K_{\\Omega}\\le B_{\\rm skel}-B_{\\rm win}-B_R"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:Theta", title := "Finite-size packing threshold", nodeIds := [53] },
        { label := "prop:entropy-high-theta", title := "Small-budget entropy closure", nodeIds := [53, 54] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node53-accumulated-decision"
          title := "Exact branch-preserving remaining-budget split"
          role := .compositionProvenance
          explanation := "Core acts on the literal node-[50] low constructor retained beside node [52], preserves the high continuation, and executes the complementary comparison only there. The Erdős layer supplies the exact manuscript bit expressions and no predecessor plumbing."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode53,
            `Erdos64EG.Internal.node53SkeletonBits,
            `Erdos64EG.Internal.node53WindowBits,
            `Erdos64EG.Internal.node53RemainderBits,
            `Erdos64EG.Internal.node53RemainingNoncurvatureBits,
            `Erdos64EG.Internal.node53ForcedCurvatureBits,
            `Erdos64EG.Internal.Node53Small,
            `Erdos64EG.Internal.Node53Large,
            `Erdos64EG.Internal.Node53Stage,
            `Erdos64EG.Internal.node53P13RemainingBudgetDecision,
            `Erdos64EG.Internal.node53LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
          ]
        }
      ]
      scopeNotes := "Node [53] performs only the diagrammed dichotomy. Its decision is kernel-checked but remains partial through inherited missing obligations; node [54] and node [55] consume its two constructors separately."
      workBound := "One proof-level real-order comparison; no graph family, state family, product, context, assignment, or Boolean universe is evaluated."
    },
    {
      stepId := "erdos.large-budget-residual-handoff"
      stageId? := some "proof-slice.p13-large-budget-residual"
      title := "Accumulated node-[55] large-budget residual"
      plainExplanation := "Node [55] is exactly the nested no leaf of node [53] after node [54] terminalizes the other two leaves. It is a zero-copy alias of the framework's focused residual and adds no inequality or density-cap claim."
      formalStatement := "K_{\\Omega}\\le B_{\\rm skel}-B_{\\rm win}-B_R\\Longrightarrow\\mathsf{ResidualC}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "rem:closure-robust", title := "Large-budget residual", nodeIds := [55] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node55-nested-large-leaf"
          title := "Framework-owned nested no-edge continuation"
          role := .compositionProvenance
          explanation := "The framework carries all earlier outputs and branch proofs. Node [55] gives the surviving leaf its paper name using the generic stage retrieval operation; no application output or handoff object is created."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode55,
            `Erdos64EG.Internal.Node55ResidualC,
            `Erdos64EG.Internal.Node55Stage,
            `Erdos64EG.Internal.node55P13LargeBudgetResidual,
            `Erdos64EG.Internal.node55LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.usingStage
          ]
        }
      ]
      scopeNotes := "Node [55] proves no quarter cap and retrieves no node-[24] density theorem. Its local zero-copy marker is kernel-checked but remains yellow through the inherited conditional chain."
      workBound := "Zero checks; only accumulated branch transport."
    },
    {
      stepId := "erdos.large-budget-net-cap"
      stageId? := some "proof-slice.p13-net-deficiency-cap"
      title := "Accumulated node-[56] large-budget net cap"
      plainExplanation := "On the exact node-[55] leaf, node [56] records the paper's finite error-bearing net-deficiency cap and proves symbolically that its exact rational coefficient tau_win is below one quarter. During migration the already proved finite cap is reused through one certificate indexed by that literal Residual C leaf."
      formalStatement := "\\frac{D^+(R)-\\sigma_R}{|R|}\\le\\tau_{\\rm win}+o(1)<\\frac14"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:p13-density", title := "Window-only P13 density handoff", nodeIds := [24] },
        { label := "rem:closure-robust", title := "Closure without forced curvature cost", nodeIds := [55, 56] },
        { label := "lem:netcharge-superadd", title := "Net-charge quarter handoff", nodeIds := [56] }
      ]
      declarationGroups := [{
        groupId := "p13-node56-ledger-net-cap"
        title := "Exact Residual C net-cap continuation"
        role := .compositionProvenance
        explanation := "Core continues only the focused Residual C leaf. The Erdős layer defines the paper's numerator, finite error, and exact coefficient; the finite-cap proof at those exact indices remains missing."
        declarations := [
          `Erdos64EG.Internal.runInitialThroughNode56,
          `Erdos64EG.Internal.node56NetDeficiencyNumerator,
          `Erdos64EG.Internal.node56TauWindow,
          `Erdos64EG.Internal.node56NetError,
          `Erdos64EG.Internal.Node56Output,
          `Erdos64EG.Internal.node56TauWindow_lt_quarter,
          `Erdos64EG.Internal.Node56Stage,
          `Erdos64EG.Internal.node56P13NetDeficiencyCap,
          `Erdos64EG.Internal.node56LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
        ]
      }]
      scopeNotes := "The exact coefficient theorem and framework continuation are kernel-checked. The finite net-cap producer remains missing and is not cited as proved evidence."
      workBound := "Zero graph checks and constant-size rational arithmetic; no graph, state, context, product, assignment, or Boolean universe is enumerated."
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
            `Erdos64EG.Internal.sparseSurplusLedgerStage,
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
            `Erdos64EG.Internal.surplusPairLedger,
            `Erdos64EG.Internal.surplusPairTransition_profile_id,
            `Erdos64EG.Internal.surplusPairTransition_context_preserved,
            `StructuralExhaustion.Routes.CT6ToCT9.advance
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
          `Erdos64EG.Internal.highCenterStructureLedgerStage,
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
          `StructuralExhaustion.Routes.Accumulated.OutputLedger,
          `StructuralExhaustion.Routes.Accumulated.advanceCurrent,
          `StructuralExhaustion.Graph.SurplusPortActivity.verifiedClassificationStage,
          `Erdos64EG.Internal.exists_verifiedSurplusPortClassificationPrefix,
          `Erdos64EG.Internal.surplusPortClassificationStage,
          `Erdos64EG.Internal.surplusPortClassificationLedger,
          `Erdos64EG.Internal.surplusPortClassificationTransition_profile_id,
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
          `StructuralExhaustion.Routes.Accumulated.OutputLedger,
          `StructuralExhaustion.Routes.Accumulated.advanceCurrent,
          `StructuralExhaustion.Graph.SurplusPortActivity.verifiedOpenPairStage,
          `Erdos64EG.Internal.exists_verifiedOpenPortPairPrefix,
          `Erdos64EG.Internal.openPortPairStage,
          `Erdos64EG.Internal.openPortPairLedger,
          `Erdos64EG.Internal.openPortPairTransition_profile_id,
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
          `StructuralExhaustion.Routes.CT9ToCT7.advance,
          `StructuralExhaustion.Graph.OpenPortResponse.transition_profile_id,
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
          `StructuralExhaustion.Graph.DegreeFourFanLedger.verifiedExecutionStage,
          `StructuralExhaustion.Graph.FiniteCertificateMarking.Profile.marked_or_residual_of_execution,
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
          `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.verifiedExecutionStage,
          `StructuralExhaustion.Graph.SelectedSurplusMass.Profile.selectedCount_le_totalSurplus,
          `Erdos64EG.Internal.TypeBSupportScope.localFanMass,
          `Erdos64EG.Internal.TypeBSupportScope.overlapCenters_card_eq_selected_length,
          `Erdos64EG.Internal.TypeBSupportScope.localFanMassRoute,
          `Erdos64EG.Internal.exists_verifiedTypeBLocalFanMassPrefix
        ]
      }]
      scopeNotes := "Node [84] consumes exactly green node [75] and nodes [81]--[83]. It proves only the local per-scope mass statement. The unsupported canonical ordinary/grouped family and coefficient 208 are retained as an open internal obligation of node [84]."
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
        { label := "lem:typeB-processed-boundary-bound", title := "Processed-envelope boundary bound", nodeIds := [84] },
        { label := "prop:typeB-bridge-sublinear", title := "Global grouped Type B fan-mass discharge", nodeIds := [84] }
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
          `StructuralExhaustion.Routes.CT5ToCT14.advance,
          `StructuralExhaustion.Routes.CT5ToCT14.transition_profile_id,
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
          `StructuralExhaustion.Routes.CT14ToCT14.advance,
          `StructuralExhaustion.Routes.CT14ToCT14.transition_profile_id,
          `StructuralExhaustion.Graph.HybridFanIncidence.other_injective,
          `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card,
          `StructuralExhaustion.Graph.HybridFanIncidence.incidence_card_le_twice_vertices,
          `StructuralExhaustion.Graph.HybridFanIncidence.multiplicity_partition,
          `StructuralExhaustion.Graph.HybridFanIncidence.total_credit_pays_deficit_with_three_slack,
          `StructuralExhaustion.Graph.HybridFanIncidence.nonWindow_credit_pays_remaining,
          `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage,
          `Erdos64EG.Internal.hybridFanIncidenceStageAt,
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
          `Erdos64EG.Internal.directFanWindowLedgerStage,
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
          `Erdos64EG.Internal.twoWindowCycleLedgerStage,
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
          `Erdos64EG.Internal.runFanLabelPackingCT9,
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
          `Erdos64EG.Internal.runMarkedFanLabelPackingCT9,
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
          `Erdos64EG.Internal.runCertificateClosedFanCT14,
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
          `Erdos64EG.Internal.verifiedPositiveDeficitFanEntryPrefix,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.degree_le_eight,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.two_le_closedCount,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.positiveDeficit,
          `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays,
          `Erdos64EG.Internal.hybridFanIncidenceStageAt,
          `Erdos64EG.Internal.PositiveDeficitFanFacts,
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
        explanation := "The reusable graph layer derives each response from CT2 bridgelessness and packed minimality, retains the exact local support, proves that the activated schedule is the unchanged CT6 schedule, and bounds one pass over only those slots and their supplied path certificates cubically. The Erdős layer supplies only the power-of-two length interpretation and the selected minimal context."
        declarations := [
          `StructuralExhaustion.Graph.SurplusPortActivation.verifiedActivatedStageFromMinimality,
          `StructuralExhaustion.Graph.SurplusPortActivation.activatedSchedule_length_eq_residualTotal,
          `Erdos64EG.Internal.surplusPortActivationSetup,
          `Erdos64EG.Internal.activatedSurplusStage,
          `Erdos64EG.Internal.activeSurplusDemand,
          `Erdos64EG.Internal.activatedSurplusSchedule_length_eq_sigma,
          `Erdos64EG.Internal.activatedSurplusWork_le_cubic,
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
      scopeNotes := "Node [144] consumes only the exact green predecessor overload and homogeneous audit. It has no quadratic branch and does not assert attachment alignment, a sparse exit, Type B entry, CT3 response equivalence, or the near-cubic spine. Its exact trigger is consumed by the verified finite classifier at node [144]; the stronger semantic obligations remain retained as an open internal obligation of node [144]."
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
        { label := "lem:same-token-semantic-bottleneck-classification", title := "Finite semantic-bottleneck classification", nodeIds := [144] },
        { label := "rem:same-token-semantic-bottleneck-classification-scope", title := "Semantic-classifier scope", nodeIds := [144] }
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
      scopeNotes := "Node [144] proves only the exhaustive finite mismatch/alignment and four-shape classification. It does not turn any leaf into a sparse exit, CT3 response equivalence, decorated Type B handoff, fixed cap, or near-cubic spine; those implications remain an open internal obligation of node [144]."
      workBound := "Exactly 234p+7 primitive checks, bounded by 234|V|+7: three local predicate comparisons per one of 78p retained coordinates and seven CT10 table checks. No ambient path, context, quotient, subgraph, graph, coloring, or universe is enumerated."
    },
    {
      stepId := "erdos.same-token-semantic-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-local-consumer"
      title := "Local semantic-bottleneck separator split"
      plainExplanation := "Node [144] consumes all five exact node-[144] leaves. Mismatch and prefix leaves remain unchanged; root and after-edge divergence expose literal distinct incidences and branch only on the locally computed separator degree."
      formalStatement := "\\text{node-[144] leaf}\\Longrightarrow\\text{retained leaf or cubic/high local separator}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-local-semantic-consumer", title := "Local semantic-bottleneck separator split", nodeIds := [144] }
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
      scopeNotes := "Node [144] proves no sparse exit, CT3 response equivalence, decorated Type B handoff, fixed cap, or near-cubic spine. Those stronger implications remain an open internal obligation of node [144]."
      workBound := "At most |V|+1 local incidence/degree checks. No path, context, quotient, subgraph, graph, coloring, or universe family is enumerated."
    },
    {
      stepId := "erdos.same-token-geometric-closure-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-switch-normalization"
      title := "Cubic switch normalization"
      plainExplanation := "This node-[144] support stage consumes its predecessor exactly. Cubic divergence leaves become literal four-vertex cubic-star data; high leaves retain degree at least four, and mismatch/prefix leaves pass through unchanged."
      formalStatement := "\\text{node-[144] frontier}\\Longrightarrow\\text{literal cubic star or retained residual}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "lem:same-token-cubic-switch-normalization", title := "Cubic switch normalization", nodeIds := [144] }
      ]
      declarationGroups := [{
        groupId := "same-token-switch-normalization-total"
        title := "Exact seven-way normalized frontier"
        role := .semanticTheorem
        explanation := "The graph layer repackages only already proved incidences and degree branches. The application proves exact node-[144] provenance, result equality, totality, and zero new checks."
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
      scopeNotes := "Node [144] proves no sparse exit, CT3 equivalence, Type B handoff, fixed cap, or near-cubic spine; those remain an open internal obligation of node [144]."
      workBound := "Zero new primitive checks; no ambient family is enumerated."
    },
    {
      stepId := "erdos.same-token-normalized-geometric-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-local-projection"
      title := "Local separator projection"
      plainExplanation := "This node-[144] support stage consumes its predecessor exactly, projecting cubic leaves to literal switch-boundary support and high leaves to their declared local port rows."
      formalStatement := "\\text{node-[144]}\\Longrightarrow\\text{switch boundary or high-port row}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-local-separator-projection", title := "Local separator projection", nodeIds := [144] }]
      declarationGroups := [{
        groupId := "same-token-local-projection"
        title := "Exact cubic/high projection"
        role := .semanticTheorem
        explanation := "All seven node-[144] leaves are retained with literal local support and port cardinality."
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
      scopeNotes := "Node [144] proves no sparse exit, response equality, CT3, Type B, fixed cap, fan safety, or target closure; those remain an open internal obligation of node [144]."
      workBound := "At most |V| local declared-port checks."
    },
    {
      stepId := "erdos.same-token-local-projection-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-strong-frontier"
      title := "Strong-semantic obligation frontier"
      plainExplanation := "Node [144] retains every exact node [144] payload and tags it with the next required theorem: sparse exit, fixed caps, CT3, or Type B. The tags are not certificates."
      formalStatement := "\\text{node-[144] leaf}\\Longrightarrow\\text{retained payload with pending obligation tag}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-strong-semantic-obligation-frontier", title := "Strong-semantic obligation frontier", nodeIds := [144] }]
      declarationGroups := [{
        groupId := "same-token-strong-obligation-frontier"
        title := "Exact seven-leaf obligation tagging"
        role := .semanticTheorem
        explanation := "The classifier retains the exact projected payload and records only its required downstream theorem. The application proves node-[144] equality, retention, totality, and constant local work."
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
      scopeNotes := "Node [144] proves no sparse exit, CT3 equivalence, Type B handoff, or fixed cap; those remain an open internal obligation of node [144]."
      workBound := "One constructor inspection; no ambient family is enumerated."
    },
    {
      stepId := "erdos.same-token-strong-semantic-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-first-clause"
      title := "First local separator clause"
      plainExplanation := "Node [144] retains node [144]'s exact payload and tag. Cubic leaves expose three exact boundary incidences; high leaves expose four distinct adjacent declared ports."
      formalStatement := "\\text{node-[144] payload}\\Longrightarrow\\text{fixed-arity literal separator data}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-first-local-separator-clause", title := "First local separator clause", nodeIds := [144] }]
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
      scopeNotes := "Node [144] discharges no sparse-exit, CT3, Type B, fixed-cap, response, or target conclusion; node [144] records the terminal pairwise-clause residual."
      workBound := "At most four literal local positions."
    },
    {
      stepId := "erdos.same-token-first-clause-consumer"
      stageId? := some "proof-slice.semantic-bottleneck-pairwise-clause"
      title := "Pairwise local separator clause"
      plainExplanation := "Node [144] preserves node [144] and the pending obligation exactly, deriving only pairwise boundary or endpoint inequalities from the retained fixed-arity local data."
      formalStatement := "\\text{node-[144] local clause}\\Longrightarrow\\text{pairwise local inequalities plus unchanged residual}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [{ label := "lem:same-token-pairwise-local-separator-clause", title := "Pairwise local separator clause", nodeIds := [144] }]
      declarationGroups := [{
        groupId := "same-token-pairwise-local-clause"
        title := "Pairwise fixed-arity separator facts"
        role := .semanticTheorem
        explanation := "The local graph layer derives pairwise distinctness and center-to-boundary inequalities; the application proves exact node-[144] and pending-obligation provenance."
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
      problemDeclaration := `Erdos64EG.Internal.hybridFanIncidenceStageAt
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.HybridFanIncidence.verifiedStage
    },
    {
      bindingId := "proof-slice.ct1-direct-fan-window"
      stageId := "proof-slice.direct-fan-window"
      tacticId := "CT1"
      role := "same-window direct-cycle elimination"
      description := "The application supplies only its selected target-avoiding context. The graph layer turns every exact closed-pair violation into a literal simple cycle and derives direct-cycle-freeness through the zero-check CT1 avoiding execution."
      problemDeclaration := `Erdos64EG.Internal.directFanWindowLedgerStage
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.FanWindowCycle.verifiedAvoidingStage
    },
    {
      bindingId := "proof-slice.ct1-two-window-cycle"
      stageId := "proof-slice.two-window-cycle"
      tacticId := "CT1"
      role := "two-window direct-cycle elimination"
      description := "The graph layer joins two vertex-disjoint induced windows with symbolic orientation-independent bridges and derives the exact target exclusion through the zero-check CT1 avoiding execution."
      problemDeclaration := `Erdos64EG.Internal.twoWindowCycleLedgerStage
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
        `Erdos64EG.Internal.PositiveDeficitMarkedFan.hybrid_credit_pays
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
