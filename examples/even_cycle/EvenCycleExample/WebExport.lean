import EvenCycleExample
import StructuralExhaustion.Canonical.ExampleExport

namespace EvenCycleExample.WebExport

open StructuralExhaustion.Canonical

private def mainWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "main"
  title := "Minimum degree three gives an even cycle"
  purpose :=
    "Follow the complete CT6→CT9 construction, its cycle certificate, and the independent CT1 validation lane."
  completion := .complete
  stages := [
    {
      stageId := "main.problem"
      title := "Endpoint-parity problem"
      summary :=
        "The graph profile supplies the minimum-degree baseline and even-cycle target used by every downstream stage."
      kind := .problem
      primaryDeclaration := `EvenCycleExample.endpointParityProfile
      evidenceDeclarations := [
        `EvenCycleExample.Baseline,
        `EvenCycleExample.HasEvenCycle
      ]
    },
    {
      stageId := "main.ct6"
      title := "CT6 maximal-path ledger"
      summary :=
        "CT6 searches the chosen maximal path and returns the active-ledger residual at its endpoint."
      kind := .tactic
      tacticId? := some "CT6"
      primaryDeclaration := `EvenCycleExample.ct6Run
      evidenceDeclarations := [
        `EvenCycleExample.ct6_no_failure,
        `EvenCycleExample.ct6_endpoint_closed,
        `EvenCycleExample.ConcreteK4.ct6_terminal_activeLedger,
        `EvenCycleExample.ConcreteK4.ct6_trace_exact
      ]
    },
    {
      stageId := "main.ct9"
      title := "CT9 parity overload"
      summary :=
        "The registered route converts endpoint-neighbor positions into a capacity-one parity instance for CT9."
      kind := .tactic
      tacticId? := some "CT9"
      primaryDeclaration := `EvenCycleExample.ct9Run
      evidenceDeclarations := [
        `EvenCycleExample.ct6ToCT9ItemAdapter,
        `EvenCycleExample.ct9_three_le_item_cardinality,
        `EvenCycleExample.ConcreteK4.ct9_terminal_overloaded,
        `EvenCycleExample.ConcreteK4.ct9_trace_exact
      ]
    },
    {
      stageId := "main.certificate"
      title := "Even-cycle certificate"
      summary :=
        "Equal-parity endpoint positions determine a chord cycle with certified even length."
      kind := .certificate
      primaryDeclaration := `EvenCycleExample.evenCycleCertificate
      evidenceDeclarations := [
        `EvenCycleExample.ConcreteK4.extracted_even_cycle_support,
        `EvenCycleExample.ConcreteK4.extracted_even_cycle_length
      ]
    },
    {
      stageId := "main.ct1"
      title := "CT1 certificate validation"
      summary :=
        "CT1 validates the already constructed cycle against the finite target encoding."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `EvenCycleExample.finalCT1Run
      evidenceDeclarations := [
        `EvenCycleExample.ConcreteK4.ct1_terminal_c1,
        `EvenCycleExample.ConcreteK4.ct1_trace_exact
      ]
    },
    {
      stageId := "main.theorem"
      title := "Even-cycle theorem"
      summary :=
        "The public theorem concludes that every finite graph of minimum degree at least three has an even simple cycle."
      kind := .theorem
      primaryDeclaration := `EvenCycleExample.minimumDegreeThree_hasEvenCycle
      evidenceDeclarations := [`EvenCycleExample.hasEvenCycle_of_minDegree_three]
    }
  ]
  links := [
    {
      linkId := "main.problem-ct6"
      sourceStageId := "main.problem"
      targetStageId := "main.ct6"
      kind := .sharedProblem
      label := "instantiates CT6"
      description := "The endpoint-parity profile generates the CT6 specification, capability, and maximal-path input."
    },
    {
      linkId := "main.ct6-ct9"
      sourceStageId := "main.ct6"
      targetStageId := "main.ct9"
      kind := .registeredRoute
      label := "active-ledger route"
      description := "The framework-registered CT6 active-ledger residual route constructs the CT9 input through the problem adapter."
      routeId? := some "CT6.residual.activeLedger->CT9"
      automationDeclarations := [
        `StructuralExhaustion.Routes.CT6ToCT9.routeContract
      ]
      evidenceDeclarations := [`EvenCycleExample.ct6ToCT9ItemAdapter]
    },
    {
      linkId := "main.ct9-certificate"
      sourceStageId := "main.ct9"
      targetStageId := "main.certificate"
      kind := .proofData
      label := "overloaded parity fibre"
      description := "CT9's overloaded fibre supplies two endpoint-neighbor positions of the same parity."
      evidenceDeclarations := [`EvenCycleExample.sameParityEndpointPositions]
    },
    {
      linkId := "main.certificate-theorem"
      sourceStageId := "main.certificate"
      targetStageId := "main.theorem"
      kind := .proofData
      label := "witnesses target"
      description := "The certified chord cycle is the witness consumed by the target theorem."
      evidenceDeclarations := [`EvenCycleExample.hasEvenCycle_of_minDegree_three]
    },
    {
      linkId := "main.certificate-ct1"
      sourceStageId := "main.certificate"
      targetStageId := "main.ct1"
      kind := .validation
      label := "validated by CT1"
      description := "CT1 checks the public certificate; it does not create the CT6→CT9 witness."
    },
    {
      linkId := "main.ct1-theorem"
      sourceStageId := "main.ct1"
      targetStageId := "main.theorem"
      kind := .validation
      label := "target confirmed"
      description := "The successful CT1 run independently confirms that the constructed witness realizes the target."
    }
  ]
}

private def deletionAuditWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "ct2-audit"
  title := "Deletion-critical CT2 audit"
  purpose :=
    "Inspect the proper-subgraph and single-edge CT2 audits in a hypothetical lexicographically minimal counterexample."
  completion := .complete
  stages := [
    {
      stageId := "ct2-audit.problem"
      title := "Minimal-counterexample context"
      summary := "The same even-cycle problem is viewed through its generated deletion-only CT2 profile."
      kind := .problem
      primaryDeclaration := `EvenCycleExample.CT2Audit.deletionClosureRule
      evidenceDeclarations := [`EvenCycleExample.CT2Audit.pieces]
    },
    {
      stageId := "ct2-audit.proper-core"
      title := "CT2 no proper core"
      summary := "The certificate-driven CT2 profile checks one proper finite subgraph and proves that it cannot retain minimum degree three."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `EvenCycleExample.CT2Audit.exists_noProperCorePrefix
      evidenceDeclarations := [
        `EvenCycleExample.CT2Audit.properCoreCT2Run_terminal,
        `EvenCycleExample.CT2Audit.properCoreCT2Run_trace,
        `EvenCycleExample.CT2Audit.properCoreCT2Run_checks,
        `EvenCycleExample.CT2Audit.properSubgraph_minDegree_le_two,
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run_polynomial
      ]
    },
    {
      stageId := "ct2-audit.ct2"
      title := "CT2 heavy-dart run"
      summary := "CT2 exhausts deletion and replacement for an explicitly exhibited heavy dart."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `EvenCycleExample.CT2Audit.heavyDartRun
      evidenceDeclarations := [
        `EvenCycleExample.CT2Audit.degree_three_endpoint,
        `EvenCycleExample.CT2Audit.invariant_I1
      ]
    },
    {
      stageId := "ct2-audit.invariant"
      title := "Heavy-edge invariant"
      summary := "Every edge has an endpoint of degree exactly three in the audited minimal-counterexample context."
      kind := .theorem
      primaryDeclaration := `EvenCycleExample.CT2Audit.invariant_I1
      evidenceDeclarations := [`EvenCycleExample.CT2Audit.degree_three_endpoint]
    }
  ]
  links := [
    {
      linkId := "ct2-audit.problem-proper-core"
      sourceStageId := "ct2-audit.problem"
      targetStageId := "ct2-audit.proper-core"
      kind := .sharedProblem
      label := "certified proper subgraph"
      description := "The packed graph profile uses the same even-cycle target and checks one explicit proper-subgraph certificate without enumerating subgraphs."
    },
    {
      linkId := "ct2-audit.problem-ct2"
      sourceStageId := "ct2-audit.problem"
      targetStageId := "ct2-audit.ct2"
      kind := .sharedProblem
      label := "generated CT2 profile"
      description := "The graph support layer generates the deletion pieces, capability, and closure rule."
    },
    {
      linkId := "ct2-audit.ct2-invariant"
      sourceStageId := "ct2-audit.ct2"
      targetStageId := "ct2-audit.invariant"
      kind := .proofData
      label := "derives invariant"
      description := "The deletion-critical result rules out a dart with both endpoints heavier than degree three."
      evidenceDeclarations := [`EvenCycleExample.CT2Audit.degree_three_endpoint]
    }
  ]
}

private def seriesWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "ct3-series"
  title := "Parity-series CT3 compression"
  purpose :=
    "Inspect the independent Duffin-style series reduction and its four exact response coordinates."
  completion := .complete
  stages := [
    {
      stageId := "ct3-series.problem"
      title := "Two-terminal series problem"
      summary := "Canonical path pieces are classified by their response to four finite gluing contexts."
      kind := .problem
      primaryDeclaration := `EvenCycleExample.SeriesReduction.seriesProblem
      evidenceDeclarations := [
        `EvenCycleExample.SeriesReduction.glue,
        `EvenCycleExample.SeriesReduction.response
      ]
    },
    {
      stageId := "ct3-series.ct3"
      title := "CT3 response compression"
      summary := "CT3 computes the exact response vector and replaces a long path with its parity representative."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration := `EvenCycleExample.SeriesReduction.run
      evidenceDeclarations := [
        `EvenCycleExample.SeriesReduction.evenLong_terminal,
        `EvenCycleExample.SeriesReduction.oddLong_terminal,
        `EvenCycleExample.SeriesReduction.evenLong_trace,
        `EvenCycleExample.SeriesReduction.oddCanonical_trace,
        `EvenCycleExample.SeriesReduction.run_traceValid,
        `EvenCycleExample.SeriesReduction.run_total
      ]
    },
    {
      stageId := "ct3-series.replacement"
      title := "Target-preserving replacement"
      summary := "Equal response rows preserve the existence of an even cycle in every compatible context."
      kind := .theorem
      primaryDeclaration := `EvenCycleExample.SeriesReduction.sameResponse_preserves_target
      evidenceDeclarations := [
        `EvenCycleExample.SeriesReduction.even_series_sameResponse,
        `EvenCycleExample.SeriesReduction.odd_series_sameResponse,
        `EvenCycleExample.SeriesReduction.run_verified
      ]
    },
    {
      stageId := "ct3-series.uncompressible"
      title := "Literal packed replacement closure"
      summary := "The even-cycle package instantiates the same airtight literal-gluing CT3 stage as the Erdős proof."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration :=
        `EvenCycleExample.SeriesReduction.exists_duffinConcreteBoundariedReplacementStage
      evidenceDeclarations := [
        `EvenCycleExample.SeriesReduction.concretePackedInput,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_lexRank_lt,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.glue_preserves_minDegree,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
      ]
    }
  ]
  links := [
    {
      linkId := "ct3-series.problem-ct3"
      sourceStageId := "ct3-series.problem"
      targetStageId := "ct3-series.ct3"
      kind := .sharedProblem
      label := "instantiates CT3"
      description := "The series contract supplies CT3's pieces, contexts, rows, response function, and work bound."
    },
    {
      linkId := "ct3-series.ct3-replacement"
      sourceStageId := "ct3-series.ct3"
      targetStageId := "ct3-series.replacement"
      kind := .proofData
      label := "certified same response"
      description := "The CT3 outcome exposes a response-equivalent representative used by the replacement theorem."
      evidenceDeclarations := [`EvenCycleExample.SeriesReduction.run_verified]
    },
    {
      linkId := "ct3-series.replacement-uncompressible"
      sourceStageId := "ct3-series.replacement"
      targetStageId := "ct3-series.uncompressible"
      kind := .frameworkComposition
      label := "one certified replacement"
      description := "Literal gluing derives target transport, baseline preservation, and strict whole-graph decrease from local replacement data."
      evidenceDeclarations := [
        `StructuralExhaustion.CT3.runCertifiedCompression,
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible
      ]
    }
  ]
}

private def inducedEdgeWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "ct1-induced-edge"
  title := "Every edge is an induced P₂"
  purpose :=
    "Validate the textbook induced-edge fact through the same certificate-driven induced-path CT1 profile used by the Erdős P₁₃ stage."
  completion := .complete
  stages := [
    {
      stageId := "ct1-induced-edge.problem"
      title := "Graph with one selected edge"
      summary := "A Mathlib dart supplies two distinct adjacent vertices and therefore the canonical induced path on two vertices."
      kind := .problem
      primaryDeclaration :=
        `StructuralExhaustion.Graph.hasInducedPath_two_of_adj
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.inducedPathTwoEmbeddingOfAdj,
        `StructuralExhaustion.Graph.InducedPath.edgeCertificate
      ]
    },
    {
      stageId := "ct1-induced-edge.ct1"
      title := "CT1 induced-path validation"
      summary := "The shared proof-carrying profile validates the induced P₂ embedding with one check and the exact C1 trace."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `StructuralExhaustion.Graph.InducedPath.runEdge
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPath.runEdge_terminal,
        `StructuralExhaustion.Graph.InducedPath.runEdge_trace,
        `StructuralExhaustion.Graph.InducedPath.runEdge_verified,
        `StructuralExhaustion.Graph.InducedPath.runEdge_total,
        `StructuralExhaustion.Graph.InducedPath.runEdge_polynomial,
        `EvenCycleExample.InducedEdge.ConcreteK4.terminal_c1,
        `EvenCycleExample.InducedEdge.ConcreteK4.trace_exact,
        `EvenCycleExample.InducedEdge.ConcreteK4.one_check
      ]
    }
  ]
  links := [
    {
      linkId := "ct1-induced-edge.problem-ct1"
      sourceStageId := "ct1-induced-edge.problem"
      targetStageId := "ct1-induced-edge.ct1"
      kind := .validation
      label := "validate induced embedding"
      description := "The canonical embedding carried by the selected edge is passed directly to the shared certificate-driven CT1 runner."
      evidenceDeclarations :=
        [`StructuralExhaustion.Graph.InducedPath.edgeCertificate]
    }
  ]
}

private def maximalMatchingWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "ct12-maximal-matching"
  title := "Maximum matching by induced-P₂ packing"
  purpose :=
    "Instantiate the reusable maximum disjoint-packing CT12 profile on the textbook family of graph edges."
  completion := .complete
  stages := [
    {
      stageId := "ct12-maximal-matching.problem"
      title := "Induced-edge supports"
      summary := "Each labelled induced P₂ embedding is one edge support; support-disjoint families are matchings."
      kind := .problem
      primaryDeclaration := `StructuralExhaustion.Graph.MaximumMatching.profile
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.inducedPathTwoEmbeddingOfAdj,
        `StructuralExhaustion.Graph.InducedPathPacking.support
      ]
    },
    {
      stageId := "ct12-maximal-matching.ct12"
      title := "CT12 maximum matching audit"
      summary := "The core selects a maximum support-disjoint family and CT12 peels only that selected edge list with a vertex-linear bound."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration := `StructuralExhaustion.Graph.MaximumMatching.run
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.MaximumMatching.run_terminal_exhausted,
        `StructuralExhaustion.Graph.MaximumMatching.run_iterations_le_vertices,
        `StructuralExhaustion.Graph.MaximumMatching.run_iterations_exact,
        `StructuralExhaustion.Graph.MaximumMatching.run_trace_length_le_vertices,
        `StructuralExhaustion.Graph.MaximumMatching.maximum,
        `StructuralExhaustion.Graph.MaximumMatching.partition,
        `EvenCycleExample.MaximalMatching.ConcreteK4.exhausted,
        `EvenCycleExample.MaximalMatching.ConcreteK4.bounded
      ]
    },
    {
      stageId := "ct12-maximal-matching.remainder"
      title := "Edgeless unmatched remainder"
      summary := "Maximum implies maximal saturation, so the unmatched vertices contain no induced P₂ and hence no edge."
      kind := .theorem
      primaryDeclaration :=
        `StructuralExhaustion.Graph.MaximumMatching.remainder_no_edges
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.InducedPathPacking.remainder_free,
        `StructuralExhaustion.Graph.MaximumMatching.verifiedStage
      ]
    }
  ]
  links := [
    {
      linkId := "ct12-maximal-matching.problem-ct12"
      sourceStageId := "ct12-maximal-matching.problem"
      targetStageId := "ct12-maximal-matching.ct12"
      kind := .sharedProblem
      label := "instantiate disjoint packing"
      description := "The graph layer supplies finite edge supports and one representative endpoint; the framework derives maximum selection and the CT12 schedule."
    },
    {
      linkId := "ct12-maximal-matching.ct12-remainder"
      sourceStageId := "ct12-maximal-matching.ct12"
      targetStageId := "ct12-maximal-matching.remainder"
      kind := .proofData
      label := "maximal saturation"
      description := "The selected maximum family intersects every other induced edge, making its vertex complement edgeless."
      evidenceDeclarations := [
        `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.maximum_saturated,
        `StructuralExhaustion.Graph.InducedPathPacking.remainder_free
      ]
    }
  ]
}

private def highCenterDeletionWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "high-center-deletion"
  title := "High-center deletion charge on K₃,₄"
  purpose :=
    "Instantiate the reusable Type-B-to-Type-A charge transition on a textbook complete bipartite graph without using an external theorem."
  completion := .complete
  stages := [
    {
      stageId := "high-center-deletion.problem"
      title := "Complete bipartite K₃,₄ profile"
      summary :=
        "The three left vertices are exactly the degree-four assigned centers; every noncenter is one of the four degree-three right vertices."
      kind := .problem
      primaryDeclaration :=
        `EvenCycleExample.ConcreteK34.highCenterDeletionProfile
      evidenceDeclarations := [
        `EvenCycleExample.ConcreteK34.leftCenter_degree_at_least_four,
        `EvenCycleExample.ConcreteK34.nonleft_core_vertex_degree_eq_three
      ]
    },
    {
      stageId := "high-center-deletion.retained"
      title := "Literal edgeless retained graph"
      summary :=
        "Deleting the left part leaves exactly the four right vertices. Their induced graph is bottom, so internal minimum degree three is excluded directly."
      kind := .adapter
      primaryDeclaration :=
        `EvenCycleExample.ConcreteK34.remainingObject_internalThreeCore_free
      evidenceDeclarations := [
        `EvenCycleExample.ConcreteK34.remainingCore_eq_rightVertices,
        `EvenCycleExample.ConcreteK34.remainingObject_graph_eq_bot
      ]
    },
    {
      stageId := "high-center-deletion.bound"
      title := "Choice-free receiver-overload bound"
      summary :=
        "The same graph-owned theorem used by the Erdős Type B scope bounds negative net quarter-charge by twenty-one times assigned surplus plus the exact retained receiver overload."
      kind := .theorem
      primaryDeclaration :=
        `EvenCycleExample.ConcreteK34.highCenterDeletion_deficit_bound
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.HighCenterDeletionCharge.Profile.neg_netQuarterCharge_le_twentyOne_mul_surplus_add_overload
      ]
    }
  ]
  links := [
    {
      linkId := "high-center-deletion.problem-retained"
      sourceStageId := "high-center-deletion.problem"
      targetStageId := "high-center-deletion.retained"
      kind := .proofData
      label := "delete all high centers"
      description :=
        "The profile's derived remaining support is exactly the right side of K₃,₄."
    },
    {
      linkId := "high-center-deletion.retained-bound"
      sourceStageId := "high-center-deletion.retained"
      targetStageId := "high-center-deletion.bound"
      kind := .frameworkComposition
      label := "apply generic charge theorem"
      description :=
        "Direct internal-core freeness supplies the sole premise needed by the reusable receiver-overload inequality."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "even-cycle"
  title := "Even cycle"
  summary :=
    "A complete minimum-degree-three proof with a registered CT6→CT9 route, CT1 validation, and separate CT2, CT3, induced-path CT1, maximum-packing CT12, and high-center-deletion reuse workflows."
  proofStatus := .complete
  workflows := [mainWorkflow, deletionAuditWorkflow, seriesWorkflow,
    inducedEdgeWorkflow, maximalMatchingWorkflow, highCenterDeletionWorkflow]
  interfaceBindings := [
    {
      bindingId := "main.ct6-capability"
      stageId := "main.ct6"
      tacticId := "CT6"
      role := "capability"
      description := "The endpoint-parity profile supplies the problem-specific CT6 failure predicate and branch enumeration."
      problemDeclaration := `EvenCycleExample.ct6Capability
      frameworkDeclaration := `StructuralExhaustion.CT6.run
    },
    {
      bindingId := "main.ct9-adapter"
      stageId := "main.ct9"
      tacticId := "CT9"
      role := "route adapter"
      description := "The item adapter gives the registered route the graph-specific endpoint-neighbor semantics required by CT9."
      problemDeclaration := `EvenCycleExample.ct6ToCT9ItemAdapter
      frameworkDeclaration := `StructuralExhaustion.Routes.CT6ToCT9.routeContract
    },
    {
      bindingId := "main.ct1-target"
      stageId := "main.ct1"
      tacticId := "CT1"
      role := "target encoding"
      description := "The graph target encoding turns an even-cycle certificate into CT1's finite realization interface."
      problemDeclaration := `EvenCycleExample.ct1TargetBridge
      frameworkDeclaration := `StructuralExhaustion.CT1.run
    },
    {
      bindingId := "ct2-audit.proper-core"
      stageId := "ct2-audit.proper-core"
      tacticId := "CT2"
      role := "certificate-driven proper-subgraph reduction"
      description := "The even-cycle package instantiates the reusable packed minimum-degree cycle profile and its constant-work certified reduction runner."
      problemDeclaration := `EvenCycleExample.CT2Audit.packedStaticInput
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run
    },
    {
      bindingId := "ct2-audit.capability"
      stageId := "ct2-audit.ct2"
      tacticId := "CT2"
      role := "deletion capability"
      description := "The generated deletion-only capability connects graph edge deletion to the generic CT2 runner."
      problemDeclaration := `EvenCycleExample.CT2Audit.capability
      frameworkDeclaration := `StructuralExhaustion.CT2.run
    },
    {
      bindingId := "ct3-series.contract"
      stageId := "ct3-series.ct3"
      tacticId := "CT3"
      role := "target-compression contract"
      description := "The series contract provides every problem-specific coordinate, response, admissibility, and complexity field consumed by CT3."
      problemDeclaration := `EvenCycleExample.SeriesReduction.contract
      frameworkDeclaration := `StructuralExhaustion.CT3.run
    },
    {
      bindingId := "ct3-series.boundaried-replacement"
      stageId := "ct3-series.uncompressible"
      tacticId := "CT3"
      role := "literal packed boundaried replacement"
      description := "The two-terminal transfer consumes the exact literal-gluing graph profile used by the Erdős stage."
      problemDeclaration := `EvenCycleExample.SeriesReduction.concretePackedInput
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.verifiedStage
    },
    {
      bindingId := "ct1-induced-edge.profile"
      stageId := "ct1-induced-edge.ct1"
      tacticId := "CT1"
      role := "certificate-driven induced-path realization"
      description := "A selected edge supplies the concrete induced P₂ embedding; the graph profile provides the same CT1 encoding, runner, semantic theorem, trace, totality, and constant budget used for induced P₁₃."
      problemDeclaration := `StructuralExhaustion.Graph.InducedPath.edgeProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.InducedPath.Profile.encoding
    },
    {
      bindingId := "ct12-maximal-matching.profile"
      stageId := "ct12-maximal-matching.ct12"
      tacticId := "CT12"
      role := "maximum disjoint finite-support packing"
      description := "Induced P₂ embeddings provide graph-specific supports; the same core maximum theorem and CT12 selected-list audit used by the Erdős P₁₃ packing provide the matching result."
      problemDeclaration := `StructuralExhaustion.Graph.MaximumMatching.profile
      frameworkDeclaration :=
        `StructuralExhaustion.CT12.DisjointPacking.Profile.verifiedStage
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `EvenCycleExample `EvenCycleExample.WebExport.descriptor descriptor

end EvenCycleExample.WebExport
