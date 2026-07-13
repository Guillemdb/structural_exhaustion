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
    "Inspect the separate deletion-only audit that derives the heavy-edge invariant in a hypothetical minimal counterexample."
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
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "even-cycle"
  title := "Even cycle"
  summary :=
    "A complete minimum-degree-three proof with a registered CT6→CT9 route, CT1 validation, and separate CT2 and CT3 auxiliary workflows."
  proofStatus := .complete
  workflows := [mainWorkflow, deletionAuditWorkflow, seriesWorkflow]
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
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `EvenCycleExample `EvenCycleExample.WebExport.descriptor descriptor

end EvenCycleExample.WebExport
