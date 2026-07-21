import Erdos64EG
import Erdos64EG.Node20
import Erdos64EG.Node56
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
        `Erdos64EG.Internal.powerOfTwoLength_iff
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
        `Erdos64EG.Internal.node6MersenneDecision,
        `Erdos64EG.Internal.node7CloseTarget,
        `Erdos64EG.Internal.node7PowerOfTwoCycle,
        `Erdos64EG.Internal.node7_avoids,
        `StructuralExhaustion.CT1.ResidualRefinement.DependentCertificateFamily.closePublicTargetContinueAvoidingUsingStage
      ]
    },
    {
      stageId := "proof-slice.no-proper-core"
      title := "CT2 no proper core"
      summary := "A supplied proper finite subgraph is one certified local reduction; target transport and lexicographic minimality force its minimum degree to be at most two."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode8
      evidenceDeclarations := [
        `Erdos64EG.Internal.node8NoProperCore,
        `Erdos64EG.Internal.node8_noProperCore,
        `Erdos64EG.Internal.node8_ct2_certificate,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_total,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_polynomial,
        `Erdos64EG.Internal.Node7Stage,
        `Erdos64EG.Internal.Node8Stage
      ]
    },
    {
      stageId := "proof-slice.ct2"
      title := "Routed CT2 deletion criticality"
      summary := "The certified CT1 residual enters local CT2 discovery; its exact disabled result forces every edge to have a degree-three endpoint."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode9
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.deletionCriticalityFacts,
        `Erdos64EG.Internal.node9DeletionCriticality,
        `Erdos64EG.Internal.node9_everyEdgeTouchesDegreeThree,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.slackVerticesIndependent_of_tightEndpoint,
        `Erdos64EG.Internal.node10HighDegreeIndependence,
        `Erdos64EG.Internal.node10_highDegreeVerticesIndependent,
        `Erdos64EG.Internal.runInitialThroughNode10,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapStage,
        `Erdos64EG.Internal.Node9Stage,
        `Erdos64EG.Internal.Node10Stage
      ]
    },
    {
      stageId := "proof-slice.ct3"
      title := "CT3 boundaried replacement"
      summary := "Literal packed-graph CT3 gluing derives whole-rank decrease, minimum-degree preservation, and target transport from local replacement data."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode11
      evidenceDeclarations := [
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
        `Erdos64EG.Internal.node14_uncompressible,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_terminal,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_trace,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_total,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_checks,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run_polynomial,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapStage,
        `Erdos64EG.Internal.node11BoundariedAtoms,
        `Erdos64EG.Internal.node12ContextUniversality,
        `Erdos64EG.Internal.node13Replacement,
        `Erdos64EG.Internal.node14Uncompressibility,
        `Erdos64EG.Internal.runInitialThroughNode12,
        `Erdos64EG.Internal.runInitialThroughNode13,
        `Erdos64EG.Internal.runInitialThroughNode14
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
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideUsingStage,
        `Erdos64EG.Internal.node15P13Decision,
        `Erdos64EG.Internal.node15_exhaustive,
        `Erdos64EG.Internal.runInitialThroughNode15,
        `Erdos64EG.Internal.node15LocalChecks_eq_zero,
        `Erdos64EG.Internal.node16_hss_target,
        `Erdos64EG.Internal.node16_hss_closure,
        `Erdos64EG.Internal.node16HSSContinuation,
        `Erdos64EG.Internal.node16LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes,
        `Erdos64EG.Internal.Node15Stage,
        `Erdos64EG.Internal.Node16Stage
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
        `Erdos64EG.Internal.node17_maximal,
        `Erdos64EG.Internal.node17_nonempty,
        `Erdos64EG.Internal.Node17Output,
        `Erdos64EG.Internal.node17InducedP13Packing,
        `Erdos64EG.Internal.node17_terminal,
        `Erdos64EG.Internal.node17Total,
        `Erdos64EG.Internal.node17WorkBudget,
        `Erdos64EG.Internal.Node17Stage,
        `Erdos64EG.Internal.Node17StageContext,
        `Erdos64EG.Internal.node17Windows,
        `Erdos64EG.Internal.node17PackingNumber
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
        `Erdos64EG.Internal.Node18Output.actualLabelsLegal,
        `Erdos64EG.Internal.Node18Stage,
        `Erdos64EG.Internal.Node18Output,
        `Erdos64EG.Internal.Node18StageContext,
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
        `Erdos64EG.Internal.node29LocalChecks_eq_zero,
        `Erdos64EG.Internal.p13Curvature_positiveDeficiency_eq_previous,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.positiveDeficiency_le_boundaryIncidences,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderBoundaryIncidences_le_tokenCount,
        `StructuralExhaustion.Graph.InducedPathWindowLedger.remainderPositiveDeficiency_le_tokenCount,
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
        `Erdos64EG.Internal.node30LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.three_mul_card_le_wedgeCount_add_twice_deficiency,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeFloor,
        `StructuralExhaustion.Graph.PositiveDeficiencyWedge.Profile.wedgeRate_of_deficiencyRate,
        `Erdos64EG.Internal.p13Remainder_wedgeFloor
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
        `Erdos64EG.Internal.node31LocalChecks_eq_zero,
        `Erdos64EG.Internal.p13CurvatureCoordinates,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_eq_wedgeCount,
        `Erdos64EG.Internal.p13CurvatureCoordinates_card_le_cube,
        `Erdos64EG.Internal.p13CurvatureResponseProfile,
        `Erdos64EG.Internal.p13CurvatureRankProfile,
        `Erdos64EG.Internal.p13CurvatureTargetRank,
        `StructuralExhaustion.CT15.CertifiedDeterminationRank.Profile.targetRank_le_coordinates
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
        `Erdos64EG.Internal.node32P13RankDropDecision,
        `Erdos64EG.Internal.Node32RankDrop,
        `Erdos64EG.Internal.Node32FullRank,
        `Erdos64EG.Internal.Node32Stage,
        `Erdos64EG.Internal.node32LocalChecks_eq_zero,
        `Erdos64EG.Internal.node32RankDecision_exhaustive,
        `Erdos64EG.Internal.node32RankDecisionWork_eq_zero,
        `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision,
        `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision_exhaustive,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoNoAfterYes
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
        `Erdos64EG.Internal.node33LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-full-curvature-rank"
      title := "Exact full-curvature-rank residual"
      summary := "Node [34] consumes node [32]'s literal full-rank constructor as a branch marker. Core retains that constructor and the complete accumulated ledger without manufacturing a Boolean-capacity or table-product consequence."
      kind := .theorem
      tacticId? := some "CT15"
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode34
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node34Output,
        `Erdos64EG.Internal.Node34Stage,
        `Erdos64EG.Internal.node34P13FullRankResidual,
        `Erdos64EG.Internal.node34LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-multiscale-curvature"
      title := "Node [21] multi-scale curvature interface"
      summary := "Node [21] fixes the exact 91-barrier output on node [19]'s literal no continuation. Its cached finite certificates prove the semantic table, safe/flat counts, strict 118-bit rate, and polynomial work bound; Core appends that verified output to the accumulated ledger."
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
        `Erdos64EG.Internal.Node21Context
      ]
    },
    {
      stageId := "proof-slice.p13-density-handoff"
      title := "Nodes [22]--[24] exact density branch"
      summary := "From the accumulated node-[21] ledger, node [22] makes the paper's exact scalar dichotomy, node [23] records the strict yes-edge overflow without an auxiliary assumption, and node [24] retains the complementary window cap, its reusable high-entropy transformer, and the accumulated hot/cold split."
      kind := .adapter
      primaryDeclaration :=
        `Erdos64EG.Internal.runInitialThroughNode24
      evidenceDeclarations := [
        `Erdos64EG.Internal.node22DensityFamily,
        `Erdos64EG.Internal.Node22High,
        `Erdos64EG.Internal.Node22Low,
        `Erdos64EG.Internal.Node22Stage,
        `Erdos64EG.Internal.runInitialThroughNode22,
        `Erdos64EG.Internal.node22LocalChecks_eq_zero,
        `Erdos64EG.Internal.Node23Output,
        `Erdos64EG.Internal.node23StrictWindowOverflow,
        `Erdos64EG.Internal.Node23Stage,
        `Erdos64EG.Internal.runInitialThroughNode23,
        `Erdos64EG.Internal.Node24HighEntropyJointBudget,
        `Erdos64EG.Internal.Node24HighEntropyCap,
        `Erdos64EG.Internal.node24HighEntropyCap_of_jointBudget,
        `Erdos64EG.Internal.Node24HighEntropyTransformer,
        `Erdos64EG.Internal.node24HighEntropyTransformer,
        `Erdos64EG.Internal.Node24Output,
        `Erdos64EG.Internal.Node24Stage,
        `Erdos64EG.Internal.node24StageEntailsHighEntropyTransformer,
        `Erdos64EG.Internal.P13AccumulatedHotColdSplitAvailable,
        `Erdos64EG.Internal.p13AccumulatedHotColdSplitAvailable,
        `Erdos64EG.Internal.node24StageEntailsAccumulatedHotColdSplit,
        `Erdos64EG.Internal.node24LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageEntails
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
        `Erdos64EG.Internal.node35LocalChecks_eq_zero,
        `StructuralExhaustion.CT15.CertifiedDeterminationRank.Profile.pairCircuitOfRankDrop,
        `StructuralExhaustion.CT15.SupportStratifiedRank.Profile.certificate,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
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
        `Erdos64EG.Internal.node35FocusedFamily,
        `Erdos64EG.Internal.Node36Stage,
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
        `Erdos64EG.Internal.node37LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node39LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.closeActiveCursorYesContinuationFinalYes
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
        `Erdos64EG.Internal.node40LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node41LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node42LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_originalEligible
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
        `Erdos64EG.Internal.node43LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node44LocalChecks_eq_zero,
        `StructuralExhaustion.Core.OneThreeRepair.identity,
        `StructuralExhaustion.Graph.OneThreeRepair.Component.identity
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
        `Erdos64EG.Internal.node45LocalChecks_eq_zero,
        `StructuralExhaustion.Graph.SupportStratifiedFunctionalRank.Admissible.injective_of_whole
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
        `Erdos64EG.Internal.node46LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node47LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-forced-curvature-cost-split"
      title := "Forced curvature cost"
      summary := "Node [48] fixes the paper's exact curvature-cost constants on the literal node-[47] leaf. The inherited wedge supply, node-[34] full-rank inequality, and node-[24] high-entropy implication prove both finite accounting bounds; Core then transports them to the real-valued cost conclusions."
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
        `Erdos64EG.Internal.node48LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-finite-remainder-entropy"
      title := "Realized remainder-state entropy"
      summary := "Node [49] projects the current residual's compatible global completions to the fixed remainder carried by node [31]. Its state count and normalized entropy therefore range over exactly the realized remainder states, without creating an ambient graph family or enumerating a product universe."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode49
      evidenceDeclarations := [
        `StructuralExhaustion.Core.DependentOwnerGlueCapacity.RealizedProjection,
        `Erdos64EG.Internal.node49RealizedRemainderHotCapacityProfile,
        `Erdos64EG.Internal.node49_realizedRemainder_mul_hotChoices_le_skeletonCode,
        `Erdos64EG.Internal.node49CanonicalAggregate,
        `Erdos64EG.Internal.node49CanonicalAggregate_eq,
        `Erdos64EG.Internal.Node49Output,
        `Erdos64EG.Internal.Node49Output.entropyExact,
        `Erdos64EG.Internal.Node49Stage,
        `Erdos64EG.Internal.node49LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-entropy-scale-split"
      title := "Exact manuscript entropy dichotomy"
      summary := "Node [50] retains node [49]'s exact realized-state count and applies the Core-owned ordered split to the equivalent natural-power comparison n^|R| <= |G_real(R)|^10. It produces exactly the original high and strict-low edges with zero primitive inspections."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode50
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node50Bypass,
        `Erdos64EG.Internal.Node50Active,
        `Erdos64EG.Internal.Node50High,
        `Erdos64EG.Internal.Node50Low,
        `Erdos64EG.Internal.Node50Stage,
        `Erdos64EG.Internal.node50_exhaustive,
        `Erdos64EG.Internal.node50LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-high-remainder-bits"
      title := "High-entropy remainder bit contribution"
      summary := "Node [51] consumes only node [50]'s exact high power inequality and takes base-two logarithms symbolically, deriving (|R|/10) log₂ n ≤ log₂ |G_real(R)| without enumerating the realized state type."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode51
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node51Output,
        `Erdos64EG.Internal.node51Output,
        `Erdos64EG.Internal.Node51Stage,
        `Erdos64EG.Internal.node51LocalChecks_eq_zero
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
        `Erdos64EG.Internal.node52LocalChecks_eq_zero,
        `Erdos64EG.Internal.node49_realizedRemainder_mul_hotChoices_le_skeletonCode,
        `StructuralExhaustion.Core.DependentOwnerGlueCapacity.BaseProfile.base_mul_localProduct_le_codeCard,
        `StructuralExhaustion.Core.PoweredJointNormalization.Profile.withError,
        `StructuralExhaustion.Core.PoweredJointNormalization.Profile.logb_withError
      ]
    },
    {
      stageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      title := "Accumulated remaining-budget decision"
      summary := "Node [53] consumes the exact low constructor retained beside node [52], compares the literal remaining labelled-skeleton bits with the inherited full-rank curvature cost, and retains both original outgoing edges. The high branch and every earlier bypass remain unchanged."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode53
      evidenceDeclarations := [
        `Erdos64EG.Internal.node53ForcedPower,
        `Erdos64EG.Internal.node53FlatPower,
        `Erdos64EG.Internal.node53UpperPower,
        `Erdos64EG.Internal.Node53Small,
        `Erdos64EG.Internal.Node53Large,
        `Erdos64EG.Internal.Node53Stage,
        `Erdos64EG.Internal.node53LocalChecks_eq_zero
      ]
    },
    {
      stageId := "proof-slice.p13-node54-entropy-cap-closure"
      title := "Two-edge entropy-cap closure"
      summary := "Node [54] terminalizes the high node-[52] leaf and the small node-[53] leaf. The high closure is the strict reverse of node [52]'s joint budget; the small closure uses node [49]'s inherited forced product fit and Core's powered-budget transfer. The node-[53] large constructor remains the unique survivor toward node [55]."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode54
      evidenceDeclarations := [
        `Erdos64EG.Internal.node54HighTerminal,
        `Erdos64EG.Internal.node54SmallBudgetImpossible,
        `Erdos64EG.Internal.Node54Stage,
        `Erdos64EG.Internal.node54P13PartIVTerminalJoin,
        `Erdos64EG.Internal.node54HighLocalChecks_eq_zero,
        `Erdos64EG.Internal.node54SmallLocalChecks_eq_zero,
        `StructuralExhaustion.Core.FinitePoweredBudgetTransfer.forced_pow_lt_flat_pow_mul_upper,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      ]
    },
    {
      stageId := "proof-slice.p13-large-budget-residual"
      title := "Residual C large-budget handoff"
      summary := "Node [55] consumes the literal nested no leaf surviving node [54]. Core appends only the Residual-C payload: the inherited node-[22] window-density cap and the node-[53] large-budget constructor. No new case, family, or handoff is created."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode55
      evidenceDeclarations := [
        `Erdos64EG.Internal.Node55Active,
        `Erdos64EG.Internal.Node55Output,
        `Erdos64EG.Internal.Node55Stage,
        `Erdos64EG.Internal.node55P13LargeBudgetResidual,
        `Erdos64EG.Internal.node55LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
      ]
    },
    {
      stageId := "proof-slice.p13-large-budget-net-cap"
      title := "Large-budget net-deficiency cap"
      summary := "Node [56] consumes only node [55]'s Residual-C leaf. The finite cap is the node-[30] net-deficiency producer carried inside node [31]; Node [56] normalizes it to the exact τ_win coefficient and proves τ_win < 1/4 by fixed rational arithmetic."
      kind := .theorem
      primaryDeclaration := `Erdos64EG.Internal.runInitialThroughNode56
      evidenceDeclarations := [
        `Erdos64EG.Internal.node56TauWin,
        `Erdos64EG.Internal.node56TauWin_lt_quarter,
        `Erdos64EG.Internal.Node56Active,
        `Erdos64EG.Internal.Node56Output,
        `Erdos64EG.Internal.Node56Stage,
        `Erdos64EG.Internal.node56P13LargeBudgetNetCap,
        `Erdos64EG.Internal.node56LocalChecks_eq_zero,
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActiveAgain
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
      evidenceDeclarations := [
        `Erdos64EG.Internal.target_iff_official_conclusion
      ]
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
        `StructuralExhaustion.CT2.runCertifiedReduction
      ]
    },
    {
      linkId := "proof-slice.no-proper-core-ct2"
      sourceStageId := "proof-slice.no-proper-core"
      targetStageId := "proof-slice.ct2"
      kind := .frameworkComposition
      label := "same selected graph"
      description := "The node [8] output contains the existing edge-rooted CT1 and local dart-deletion CT2 prefix on its fixed exposed vertex type."
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
        `Erdos64EG.Internal.hssTarget_of_p13Free
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
      description := "Node [34] converts node [32]'s exact full-rank equality into the displayed inequality W₂(R) ≤ rΩ(R), and Core exposes that theorem through the accumulated ledger."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
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
      description := "Node [48] consumes the literal node-[47] full-rank value retrieved from the accumulated residual ledger. Its finite accounting conclusions are derived on that exact leaf; Core transports every bypass and sibling unchanged."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
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
      label := "fixed remainder to realized state projection"
      description := "The accumulated node-[48] stage fixes R. Node [49] projects the current compatible-completion residual to that remainder, while the framework retains every earlier ledger fact automatically."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
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
      label := "exact state count to manuscript power split"
      description := "Node [50] consumes the identical dependent node-[49] output and uses the framework focused-branch decision, so both original edges retain that exact realized-state count."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
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
      description := "The framework maps only node [51]'s exact high continuation. Node [52] proves the same-context joint capacity, its powered normalization, logarithmic transport, and final joint budget on that literal residual; every sibling remains unchanged."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
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
      linkId := "proof-slice.node52-node53-node54-entropy-cap-closure"
      sourceStageId := "proof-slice.p13-low-entropy-forced-cost-fit"
      targetStageId := "proof-slice.p13-node54-entropy-cap-closure"
      kind := .frameworkComposition
      label := "two incoming terminal leaves"
      description := "The framework terminalizer closes node [52]'s high leaf and node [53]'s small leaf while leaving node [53]'s large constructor as the surviving residual for node [55]."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node54P13PartIVTerminalJoin
      ]
    },
    {
      linkId := "proof-slice.node54-node55-large-budget-residual"
      sourceStageId := "proof-slice.p13-node54-entropy-cap-closure"
      targetStageId := "proof-slice.p13-large-budget-residual"
      kind := .frameworkComposition
      label := "surviving node-[53] no leaf"
      description := "Core continues the single active leaf left by node [54] and appends node [55]'s local Residual-C payload."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node55P13LargeBudgetResidual
      ]
    },
    {
      linkId := "proof-slice.node55-node56-net-deficiency-cap"
      sourceStageId := "proof-slice.p13-large-budget-residual"
      targetStageId := "proof-slice.p13-large-budget-net-cap"
      kind := .frameworkComposition
      label := "Residual C net cap"
      description := "Core bundles the literal node-[55] output with the active leaf; node [56] retrieves the retained node-[30] finite cap and normalizes it."
      automationDeclarations := [
        `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActiveAgain
      ]
      evidenceDeclarations := [
        `Erdos64EG.Internal.node56P13LargeBudgetNetCap
      ]
    },
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
    4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    22, 54, 55, 56
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
      ("N24-HOT-COLD-SPLIT", "Carry the accumulated node-[21] framework hot/cold split through node [24] as a StageEntails fact; hot consequences come only from the framework hot constructor."),
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
    ] ++ ExampleNodeObligationDescriptor.provedForStep 54
      "erdos.node54-entropy-cap-closure" [
      ("N54-52-PROV", "Consume the literal node-[52] feasibility payload from the accumulated high edge while retaining node [50]'s low edge unchanged."),
      ("N54-52-STRICT", "Identify the finite high-theta alternative as the strict reverse of node [52]'s exact error-bearing cap."),
      ("N54-52-CLOSE", "Prove the strict node-[52] high-theta leaf impossible by symbolic order arithmetic."),
      ("N54-53-PROV", "Consume the literal node-[53] strict-small constructor on the unchanged realized remainder carrier."),
      ("N54-53-CAPACITY", "Retrieve the node-[48]/[49] powered table-product fit on the literal realized remainder state carrier together with node [50]'s strict low bound."),
      ("N54-53-CLOSE", "Raise the certified product inequality to the tenth power and contradict node [53]'s reverse comparison."),
      ("N54-ROUTE", "Use Core's terminalize-and-close primitive so only node [53]'s large constructor survives toward node [55]."),
      ("N54-WORK", "Perform zero semantic checks and enumerate no graph, context, state, product, assignment, or Boolean universe.")
    ] ++ ExampleNodeObligationDescriptor.partialForStep 53
      "erdos.low-entropy-forced-cost-fit" [
      ("N53-PROV", "Consume only the exact low constructor of the accumulated node-[50] decision and preserve node [51]'s high output unchanged."),
      ("N53-BUDGET", "Define the remaining non-curvature budget from the exact labelled-skeleton, hot-window, and node-[49] constrained-family bit counts."),
      ("N53-COST", "Consume the inherited full-rank curvature cost without recomputing node [47] or node [48]."),
      ("N53-YES", "Retain the strict small-budget edge remainingBits < forcedCurvatureBits for node [54]."),
      ("N53-NO", "Retain the complementary large-budget edge forcedCurvatureBits <= remainingBits for node [55]."),
      ("N53-EXHAUSTIVE", "Use the framework no-after-yes continuation so both node-[53] edges are exhaustive on the literal node-[50] value."),
      ("N53-WORK", "Perform one proof-level real-order comparison and no graph, state, product, context, or Boolean-universe enumeration.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 55
      "erdos.large-budget-residual-handoff" [
      ("N55-PROV", "Consume the exact node-[53] complementary large-budget constructor after node [54] terminalizes the other two Part-IV leaves."),
      ("N55-MARKER", "Name the framework's already focused active value Residual C without constructing an application-owned output or handoff."),
      ("N55-BRANCH", "Expose exactly Residual C on the original node-[53] no edge, adding no inequality, density claim, case, or hypothesis."),
      ("N55-HANDOFF", "Preserve every terminal and earlier bypass while retrieving the identical focused stage through the framework."),
      ("N55-WORK", "Use zero-check framework routing and perform no mathematical recomputation or finite scan.")
    ] ++ ExampleNodeObligationDescriptor.provedForStep 56
      "erdos.large-budget-net-cap" [
      ("N56-PROV", "Consume only node [55]'s literal Residual C leaf on the same accumulated residual."),
      ("N56-DEFS", "Define the exact net-deficiency numerator, surplus error, and rational tau_win printed by the paper."),
      ("N56-FINITE", "Derive the finite error-bearing net cap from facts retrieved from the accumulated ledger on that exact leaf."),
      ("N56-QUARTER", "Evaluate the exact limiting coefficient tau_win symbolically and prove tau_win < 1/4."),
      ("N56-HANDOFF", "Continue only the focused active leaf through the framework and preserve every bypass automatically."),
      ("N56-WORK", "Perform zero local graph checks and no ambient-universe enumeration."),
      ("N56-NETCAP", "Use the node-[30] finite-cap producer carried through node [31] at the literal Residual C indices.")
    ] ++ ExampleNodeObligationDescriptor.missing 57 [
      ("N57-PROV", "Consume the exact node-[56] output from the accumulated ledger on the same eventual tail."),
      ("N57-STRICT", "Convert the normalized strict-quarter inequality to its exact denominator-free natural-number form without dropping the node-[56] error." )
    ] ++ ExampleNodeObligationDescriptor.missing 58 [
      ("N58-CHARGE", "Define the manuscript net charge as the exact quarter-scaled integer numerator on the identical remainder.")
    ] ++ ExampleNodeObligationDescriptor.missing 59 [
      ("N59-SPLIT", "Retain the strict negative constructor forced by node [57] on the exact node-[58] charge.")
    ] ++ ExampleNodeObligationDescriptor.missing 60 [
      ("N60-CLOSE", "Contradict the nonnegative edge using the identical strict negative integer charge.")
    ] ++ ExampleNodeObligationDescriptor.missing 61 [
      ("N61-DECOMP", "Use the canonical connected-component decomposition and its exact additive charge identity."),
      ("N61-CT11", "Run CT11 on that finite ordered component list and return an actual connected negative support." )
    ] ++ ExampleNodeObligationDescriptor.missing 62 [
      ("N62-SPLIT", "Inspect only the selected support's actual high centers and return exactly the original Type-A or Type-B edge.")
    ] ++ ExampleNodeObligationDescriptor.missing 63 [
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
            `Erdos64EG.Internal.node7_avoids
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
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.verifiedInducedPathStage,
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
            `StructuralExhaustion.Routes.CT1ToCT12.advance,
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
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingAttachmentPrefix,
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
        "Node [18]'s legal-label table and Cₛ/Ω₂ definitions are proved. Node [21]'s 91-barrier interface is tracked separately and remains partial until its packed-row semantics and safe/flat count obligations are proved with sole-HSS evidence."
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
          `StructuralExhaustion.Core.QuadraticScaleSplit.verifiedStage,
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
      plainExplanation := "The lightweight API fixes the exact CT10 classification, packed relation profile, safe/flat products, work expression, and node-[21] output specification on node [19]'s bounded edge. Its optimized semantic/count producer remains missing; downstream local transformations are therefore only partial evidence."
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
      scopeNotes := "Node [21] remains partial. The API is exact, but its complete semantic/count producer is still missing."
      workBound := "Fifteen fixed 399×399 bit relations and 91 quadratic barrier scans, split into 15 independently cached audit shards. The public CT10 classification uses 196 candidate checks; no graph family or Boolean cube is enumerated."
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
            `Erdos64EG.Internal.P13AccumulatedHotColdSplitAvailable,
            `Erdos64EG.Internal.p13AccumulatedHotColdSplitAvailable,
            `Erdos64EG.Internal.node24StageEntailsAccumulatedHotColdSplit,
            `Erdos64EG.Internal.node24P13DensityBounds,
            `Erdos64EG.Internal.node24LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageEntails
          ]
        }
      ]
      scopeNotes := "Nodes [22]--[24] consume node [21]'s kernel-checked accumulated stage. Node [23] is the exact local continuation of node [22]'s yes constructor and accepts no quiet-block premise. Node [24]'s scalar transformer and accumulated hot-certificate StageEntails instances are kernel-checked; node [52] separately supplies the later joint-budget premise on its own branch."
      workBound := "One proof-level natural-number dichotomy and symbolic arithmetic; no finite universe is scanned."
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
          `Erdos64EG.Internal.p13CurvatureRankProfile,
          `Erdos64EG.Internal.p13CurvatureTargetRank,
          `StructuralExhaustion.CT15.CertifiedDeterminationRank.Profile.targetRank_le_coordinates,
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
          `Erdos64EG.Internal.node32P13RankDropDecision,
          `Erdos64EG.Internal.Node32RankDrop,
          `Erdos64EG.Internal.Node32FullRank,
          `Erdos64EG.Internal.Node32Stage,
          `Erdos64EG.Internal.node32LocalChecks_eq_zero,
          `Erdos64EG.Internal.node32RankDecision_exhaustive,
          `Erdos64EG.Internal.node32RankDecisionWork_eq_zero,
          `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision,
          `StructuralExhaustion.CT15.FunctionalAdmissibleRank.Profile.rankDecision_exhaustive,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoNoAfterYes,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoYesClosedActive
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
      plainExplanation := "Node [34] consumes only node [32]'s full-rank constructor. The framework retains that exact constructor and every predecessor fact; no stronger Boolean-capacity or safe/flat table-product certificate is inferred from it."
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
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
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
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapActiveCursorDecisionYesContinuation,
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
          `Erdos64EG.Internal.node35FocusedFamily,
          `Erdos64EG.Internal.Node36Stage,
          `Erdos64EG.Internal.node36P13OriginalContextAudit,
          `Erdos64EG.Internal.node36LocalChecks_eq_zero,
          `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.OriginalContextAudit,
          `StructuralExhaustion.Core.SupportStratifiedDetermination.Profile.Certificate.auditOriginal,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideActiveCursorYesContinuation
        ]
      }]
      scopeNotes := "The local decision is kernel-checked but remains partial through node [35]'s missing support producer and earlier missing predecessors."
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
      scopeNotes := "The local focus is kernel-checked but remains partial because the node-[35] support certificate producer is missing."
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
          explanation := "The node-[48] successor consumes the exact node-[47] stage from the accumulated ledger, derives the finite accounting inequalities at that literal leaf, and lets Core own every bypass and branch transport."
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
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
          ]
        }
      ]
      scopeNotes := "Node [48] owns the two finite accounting inequalities and their two paper-local forced-cost transports. They are proved on the literal node-[47] residual from inherited ledger facts; construction of the realized remainder-state projection belongs to node [49]."
      workBound := "Zero local scans; no graph family, context universe, subset family, assignment cube, or Boolean universe is generated."
    },
    {
      stepId := "erdos.finite-remainder-state-entropy"
      stageId? := some "proof-slice.p13-finite-remainder-entropy"
      title := "Per-vertex remainder entropy"
      plainExplanation := "Node [49] restricts each compatible global completion in the current residual to the fixed remainder carried by node [31]. It takes the symbolic cardinality of that realized projection and records its normalized entropy; it introduces no ambient candidate-graph family."
      formalStatement := "\\mathcal G_{\\rm real}(R)=\\{J|_R:J\\text{ is a compatible completion in the current residual}\\},\\qquad \\eta(R)=\\frac{\\log_2|\\mathcal G_{\\rm real}(R)|}{|R|}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:remainder-entropy", title := "Per-vertex skeleton entropy of the remainder", nodeIds := [49] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node49-realized-projection"
          title := "Framework-owned realized remainder projection"
          role := .mathematicalDefinition
          explanation := "Core owns the realized projection of the exact compatible-completion residual and its dependent glue-capacity theorem. Erdős supplies only the restriction map, the canonical accumulated hot aggregate, and the entropy identity."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode49,
            `StructuralExhaustion.Core.DependentOwnerGlueCapacity.RealizedProjection,
            `Erdos64EG.Internal.node49RealizedRemainderHotCapacityProfile,
            `Erdos64EG.Internal.node49_realizedRemainder_mul_hotChoices_le_skeletonCode,
            `Erdos64EG.Internal.node49CanonicalAggregate,
            `Erdos64EG.Internal.node49CanonicalAggregate_eq,
            `Erdos64EG.Internal.Node49Output,
            `Erdos64EG.Internal.Node49Output.entropyExact,
            `Erdos64EG.Internal.Node49Stage,
            `Erdos64EG.Internal.node49P13RemainderEntropy,
            `Erdos64EG.Internal.node49LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
          ]
        }
      ]
      scopeNotes := "This node only records the realized remainder-state count and eta(R). The high/low threshold split and all consequences belong to node [50] and later nodes."
      workBound := "Zero executable semantic checks: finiteness is inherited symbolically from the current completion residual, and no graph, subgraph, context, assignment, or Boolean universe is enumerated."
    },
    {
      stepId := "erdos.entropy-scale-split"
      stageId? := some "proof-slice.p13-entropy-scale-split"
      title := "Exact manuscript entropy split"
      plainExplanation := "Node [50] consumes node [49]'s exact realized-state count and applies the framework dichotomy to the equivalent natural-power comparison. The exact predecessor and both original edges remain in the accumulated residual."
      formalStatement := "n^{|R|}\\le |\\mathcal G_{\\rm real}(R)|^{10}\\quad\\lor\\quad |\\mathcal G_{\\rm real}(R)|^{10}<n^{|R|}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "def:remainder-entropy", title := "Per-vertex remainder entropy threshold", nodeIds := [50] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node50-power-threshold"
          title := "Framework-owned natural-power threshold"
          role := .compositionProvenance
          explanation := "Core owns the exhaustive ordered split and residual transport. The Erdős layer supplies only the two exact natural powers on node [49]'s realized-state count."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode50,
            `Erdos64EG.Internal.Node50Bypass,
            `Erdos64EG.Internal.Node50Active,
            `Erdos64EG.Internal.Node50High,
            `Erdos64EG.Internal.Node50Low,
            `Erdos64EG.Internal.Node50Stage,
            `Erdos64EG.Internal.node50P13EntropyDecision,
            `Erdos64EG.Internal.node50_exhaustive,
            `Erdos64EG.Internal.node50LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
          ]
        }
      ]
      scopeNotes := "Node [50] proves only the exhaustive high/low entropy split. Node [51] must consume the high constructor, while node [53] and the later low-entropy analysis must consume the low constructor; those consumers are separate obligations."
      workBound := "Zero primitive checks. The split is logical and keeps both natural powers symbolic; no graph family, state family, subset family, context universe, function space, assignment cube, or Boolean universe is evaluated."
    },
    {
      stepId := "erdos.high-remainder-bits"
      stageId? := some "proof-slice.p13-high-remainder-bits"
      title := "High-entropy remainder bit contribution"
      plainExplanation := "Node [51] consumes node [50]'s exact high natural-power proposition on the full accumulated residual. Monotonicity and the power law for base-two logarithms give the printed remainder-bit contribution by symbolic arithmetic."
      formalStatement := "n^{|R|}\\le |\\mathcal G_{\\rm real}(R)|^{10}\\Longrightarrow (|R|/10)\\log_2 n\\le\\log_2|\\mathcal G_{\\rm real}(R)|"
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
      plainExplanation := "The framework maps only node [51]'s exact high continuation and retains every sibling unchanged. Node [52] proves its same-skeleton joint-capacity and normalized budget locally on that literal leaf."
      formalStatement := "\\text{high}_{51}\\longrightarrow\\left[\\frac{1-13\\theta}{10}+118.108581006\\,\\theta\\le1.5+o(1)\\right]"
      status := .implemented
      correspondence := .support
      manuscriptRefs := [
        { label := "prop:two-budget", title := "Two-budget routing", nodeIds := [52] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node52-accumulated-handoff"
          title := "Branch-preserving local feasibility handoff"
          role := .compositionProvenance
          explanation := "Core owns exact predecessor retention and low-edge pass-through. The Erdős layer proves the paper's same-context joint capacity, powered normalization, logarithmic transport, and final joint budget on the incoming high leaf."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode52,
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
        }
      ]
      scopeNotes := "The framework transition and every same-context capacity and normalization theorem listed above are kernel-checked on the literal node-[51] residual. Node [52] creates no decision or additional branch."
      workBound := "Zero semantic checks and no graph, context, state-product, assignment-cube, or Boolean-universe enumeration."
    },
    {
      stepId := "erdos.window-remainder-density-accounting"
      title := "Window-plus-remainder accounting"
      plainExplanation := "The remaining paper-facing density consequence must rewrite node [52]'s exact joint budget into the displayed scalar normalization and solve that scalar inequality. The same-context finite and logarithmic accounting that supplies the premise is already kernel-checked."
      formalStatement := "\\frac{1-13\\theta}{10}+118.108581006\\,\\theta\\le1.5+o(1)\\Longrightarrow\\theta\\le0.01198542083\\ldots+o(1)"
      status := .next
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:two-budget", title := "Two-budget routing", nodeIds := [52] },
        { label := "prop:p13-density", title := "Near-cubic P13 window density bounds", nodeIds := [52] }
      ]
      scopeNotes := "Framework routing and the exact finite, powered, logarithmic, and joint-budget propositions are implemented. What remains here is only the manuscript's final scalar normalization to the displayed theta bound."
      workBound := "Pure symbolic arithmetic over inherited ledger facts, with zero ambient graph, context, state-product, assignment-cube, or Boolean-universe enumeration."
    },
    {
      stepId := "erdos.node54-entropy-cap-closure"
      stageId? := some "proof-slice.p13-node54-entropy-cap-closure"
      title := "Node-[54] entropy-cap closure"
      plainExplanation := "Node [54] closes both prescribed incoming edges. The high edge is the strict reverse of node [52]'s exact joint budget. The low-small edge combines node [49]'s inherited product-cost fit with node [50]'s strict low bound through Core's powered-budget transfer, contradicting node [53]'s reverse comparison."
      formalStatement := "543958^r\\le111286^rN_R,\\quad N_R^{10}<U,\\quad111286^{10r}U\\le543958^{10r}\\Longrightarrow\\bot"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:entropy-high-theta", title := "Entropy cap closes the high-theta branch", nodeIds := [54] }
      ]
      declarationGroups := [
        {
          groupId := "p13-node54-two-edge-closure"
          title := "Verified two-edge Part-IV closure"
          role := .compositionProvenance
          explanation := "The high edge is a direct symbolic order contradiction. The low-small edge retrieves node [49]'s product-cost certificate and uses Core's generic powered-budget transfer; the terminalizer preserves the sibling large branch for node [55]."
          declarations := [
            `Erdos64EG.Internal.node54HighTerminal,
            `Erdos64EG.Internal.node54SmallBudgetImpossible,
            `Erdos64EG.Internal.Node54Stage,
            `Erdos64EG.Internal.node54P13PartIVTerminalJoin,
            `Erdos64EG.Internal.runInitialThroughNode54,
            `Erdos64EG.Internal.node54HighLocalChecks_eq_zero,
            `Erdos64EG.Internal.node54SmallLocalChecks_eq_zero,
            `StructuralExhaustion.Core.FinitePoweredBudgetTransfer.forced_pow_lt_flat_pow_mul_upper,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.terminalizeFocusedBranchYesCloseNestedYes
          ]
        }
      ]
      scopeNotes := "Node [54] is a terminal closure only. It proves exactly the [52] high-theta and [53] small-budget contradictions, and leaves the [53] large branch routed to node [55]."
      workBound := "Pure symbolic arithmetic over inherited ledger facts. No semantic checks, graph families, context families, state-product scans, assignment cubes, or Boolean universes are enumerated."
    },
    {
      stepId := "erdos.low-entropy-forced-cost-fit"
      stageId? := some "proof-slice.p13-low-entropy-forced-cost-fit"
      title := "Accumulated node-[53] budget decision"
      plainExplanation := "Node [53] consumes only node [50]'s exact low constructor. It compares the exact forced curvature power with the flat curvature power times the inherited low-entropy allowance, retaining both manuscript edges. The high constructor and node [52] output pass through unchanged."
      formalStatement := "111286^{10r}n^{|R|}\\le543958^{10r}\\quad\\text{or}\\quad543958^{10r}<111286^{10r}n^{|R|}"
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
          explanation := "Core acts on the literal node-[50] low constructor retained beside node [52], preserves the high continuation, and executes the complementary natural-power comparison only there. The Erdős layer supplies the three exact powers and no predecessor plumbing."
          declarations := [
            `Erdos64EG.Internal.runInitialThroughNode53,
            `Erdos64EG.Internal.node53ForcedPower,
            `Erdos64EG.Internal.node53FlatPower,
            `Erdos64EG.Internal.node53UpperPower,
            `Erdos64EG.Internal.Node53Small,
            `Erdos64EG.Internal.Node53Large,
            `Erdos64EG.Internal.Node53Stage,
            `Erdos64EG.Internal.node53P13RemainingBudgetDecision,
            `Erdos64EG.Internal.node53LocalChecks_eq_zero,
            `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
          ]
        }
      ]
      scopeNotes := "Node [53] performs only the diagrammed dichotomy. Its decision is kernel-checked; node [54] and node [55] consume its two constructors separately."
      workBound := "One proof-level natural-order comparison; no graph family, state family, product, context, assignment, or Boolean universe is evaluated."
    },
    {
      stepId := "erdos.large-budget-residual-handoff"
      stageId? := some "proof-slice.p13-large-budget-residual"
      title := "Accumulated node-[55] large-budget residual"
      plainExplanation := "Node [55] is exactly the nested no leaf of node [53] after node [54] terminalizes the other two leaves. It uses Core's focused active continuation to append the Residual-C payload: the inherited window-density cap and the large-budget constructor."
      formalStatement := "K_{\\Omega}\\le B_{\\rm skel}-B_{\\rm win}-B_R\\Longrightarrow\\mathsf{ResidualC}"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "rem:closure-robust", title := "Large-budget residual", nodeIds := [55] }
      ]
      declarationGroups := [{
        groupId := "p13-node55-large-budget-residual"
        title := "Framework-owned Residual-C handoff"
        role := .compositionProvenance
        explanation := "Core continues the literal surviving node-[54] active leaf. The Erdős payload contains only node [55]'s local data and no custom handoff."
        declarations := [
          `Erdos64EG.Internal.Node55Active,
          `Erdos64EG.Internal.Node55Output,
          `Erdos64EG.Internal.Node55Stage,
          `Erdos64EG.Internal.node55P13LargeBudgetResidual,
          `Erdos64EG.Internal.runInitialThroughNode55,
          `Erdos64EG.Internal.node55LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActive
        ]
      }]
      scopeNotes := "Node [55] only names the surviving large-budget residual and carries its existing local branch facts forward."
      workBound := "Zero checks; only accumulated branch transport."
    },
    {
      stepId := "erdos.large-budget-net-cap"
      stageId? := some "proof-slice.p13-large-budget-net-cap"
      title := "Accumulated node-[56] large-budget net cap"
      plainExplanation := "On the exact node-[55] leaf, node [56] retrieves the node-[30] finite net-deficiency cap carried by node [31], normalizes it to the exact tau_win coefficient, and proves tau_win < 1/4."
      formalStatement := "\\frac{D^+(R)-\\sigma_R}{|R|}\\le\\tau_{\\rm win}+o(1)<\\frac14"
      status := .implemented
      correspondence := .exact
      manuscriptRefs := [
        { label := "prop:p13-density", title := "Window-only P13 density handoff", nodeIds := [24] },
        { label := "rem:closure-robust", title := "Closure without forced curvature cost", nodeIds := [55, 56] },
        { label := "lem:netcharge-superadd", title := "Net-charge quarter handoff", nodeIds := [56] }
      ]
      declarationGroups := [{
        groupId := "p13-node56-net-cap"
        title := "Finite net cap and tau arithmetic"
        role := .semanticTheorem
        explanation := "The finite cap comes from node [30]'s producer inside the carried node-[31] payload. Node [56] performs only symbolic normalization and the exact rational comparison tau_win < 1/4."
        declarations := [
          `Erdos64EG.Internal.Node30Output.netDeficiencyFiniteCap,
          `Erdos64EG.Internal.node56TauWin,
          `Erdos64EG.Internal.node56TauWin_lt_quarter,
          `Erdos64EG.Internal.Node56Active,
          `Erdos64EG.Internal.Node56Output,
          `Erdos64EG.Internal.Node56Stage,
          `Erdos64EG.Internal.node56P13LargeBudgetNetCap,
          `Erdos64EG.Internal.runInitialThroughNode56,
          `Erdos64EG.Internal.node56LocalChecks_eq_zero,
          `StructuralExhaustion.Core.ResidualRefinement.State.StageNode.continueFocusedBranchActiveAgain
        ]
      }]
      scopeNotes := "Node [56] supplies the finite, error-bearing net-deficiency cap for the large-budget residual. The later negative-support localization is Part V."
      workBound := "Zero graph checks and constant-size rational arithmetic; no graph, state, context, product, assignment, or Boolean universe is enumerated."
    },
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
      bindingId := "proof-slice.ct10-p13-labels"
      stageId := "proof-slice.p13-labels"
      tacticId := "CT10"
      role := "exact finite attachment-label classification"
      description := "The problem supplies a compact thirteen-bit legality predicate proved equivalent to graph-theoretic cycle avoidance; the generic CT10 profile classifies the 8192 local candidates, audits the complete 399-row table, and retains a quadratic work certificate."
      problemDeclaration := `Erdos64EG.Internal.p13AttachmentClassification
      frameworkDeclaration :=
        `StructuralExhaustion.CT10.ExhaustiveClassification.Profile.verifiedStage
    },
  ]
  manuscript? := some erdosManuscript
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `Erdos64EG `Erdos64EG.WebExport.descriptor descriptor

end Erdos64EG.WebExport
