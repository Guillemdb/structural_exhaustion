import Erdos64EG
import Erdos64EG.Tests
import StructuralExhaustion.Canonical.ExampleExport

namespace Erdos64EG.WebExport

open StructuralExhaustion.Canonical

private def proofSliceWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "proof-slice"
  title := "Verified Erdős 64 prefix"
  purpose :=
    "Inspect the exact Mersenne target algebra, lexicographic minimal selection, CT2 criticality, boundaried replacement, the HSS-forced induced-P13 CT1 stage, the maximum-packing CT12 remainder stage, and the exhaustive CT10 P13 attachment-label algebra."
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
      kind := .frameworkComposition
      label := "same selected graph"
      description := "The graph profile consumes the exact CT1 induced-path realization, derives nonemptiness of the selected maximum family, runs CT12 on that family, and retains the preceding prefix unchanged."
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13PackingPrefix,
        `Erdos64EG.Internal.p13PackingPrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingPrefix
      ]
    },
    {
      linkId := "proof-slice.p13-packing-labels"
      sourceStageId := "proof-slice.p13-packing"
      targetStageId := "proof-slice.p13-labels"
      kind := .frameworkComposition
      label := "same selected graph and branch context"
      description := "The graph profile consumes the exact CT12 packing prefix unchanged, runs the complete finite label table in its inherited branch context, and proves every actual attachment label is accepted from target avoidance."
      evidenceDeclarations := [
        `Erdos64EG.Internal.verifiedP13LabelAlgebraPrefix,
        `Erdos64EG.Internal.p13LabelAlgebraPrefix_previous,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingAttachmentPrefix
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
            `Erdos64EG.Internal.p13PackingPrefix_nonempty,
            `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.inducedPathPackingPrefix
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
      stepId := "erdos.surplus-frontier"
      title := "Non-near-cubic surplus routing"
      plainExplanation :=
        "The next dependency-ready stage must route the non-near-cubic surplus branch through its finite blocker and capacity-token accounting before the proof may continue to the curvature enumeration."
      formalStatement :=
        "\\sigma(G)>C_{\\mathrm{sp}}\\sqrt n \\Longrightarrow \\text{a certified sparse-surplus exit or closure}"
      status := .next
      correspondence := .partialCoverage
      manuscriptRefs := [
        { label := "prop:nonnear-cubic-sharp-overload-routing", title := "Non-near-cubic sparse-pressure routing", nodeIds := [19, 20] }
      ]
      scopeNotes :=
        "No Lean declaration currently claims this manuscript stage. Node [21] and the later density/remainder budget are downstream and must not be presented as implemented."
      workBound := "Not yet implemented; the future CT must expose its local finite universe and polynomial audit."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "erdos-64"
  title := "Erdős Problem 64"
  summary :=
    "A partial proof with exact Mersenne returns, lexicographic minimal selection, CT2 criticality, CT3 boundaried uncompressibility, an HSS-forced induced-P13 CT1 stage, a maximum-packing CT12 remainder stage, and the complete CT10 P13 attachment-label algebra."
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
      bindingId := "proof-slice.ct10-p13-labels"
      stageId := "proof-slice.p13-labels"
      tacticId := "CT10"
      role := "exact finite attachment-label classification"
      description := "The problem supplies a compact thirteen-bit legality predicate proved equivalent to graph-theoretic cycle avoidance; the generic CT10 profile classifies the 8192 local candidates, audits the complete 399-row table, and retains a quadratic work certificate."
      problemDeclaration := `Erdos64EG.Internal.p13AttachmentClassification
      frameworkDeclaration :=
        `StructuralExhaustion.CT10.ExhaustiveClassification.Profile.verifiedStage
    }
  ]
  manuscript? := some erdosManuscript
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `Erdos64EG `Erdos64EG.WebExport.descriptor descriptor

end Erdos64EG.WebExport
