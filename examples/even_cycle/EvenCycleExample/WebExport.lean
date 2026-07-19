import EvenCycleExample
import StructuralExhaustion.Canonical.ExampleExport

namespace EvenCycleExample.WebExport

open StructuralExhaustion.Canonical

private def mainWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "main"
  title := "Minimum degree three gives an even cycle"
  purpose :=
    "Follow the framework-owned CT6→CT9 construction, its cycle certificate, and the independent CT1 validation lane."
  completion := .complete
  stages := [
    {
      stageId := "main.problem"
      title := "Endpoint-parity interface"
      summary :=
        "The application selects the reusable even-cycle profile; the framework supplies the problem, baseline, target, and CT capabilities."
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
        "The profile computes an endpoint-maximal path and returns CT6's active-ledger residual."
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
        "The graph profile turns equal-parity endpoint positions into a chord cycle with certified even length."
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
        "CT1 validates the constructed cycle against the framework-generated finite target encoding."
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
        "Every explicitly finite graph of minimum degree at least three has an even simple cycle."
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
      label := "selects profile"
      description := "The one problem-specific profile selection generates CT6's specification, capability, and maximal-path input."
    },
    {
      linkId := "main.ct6-ct9"
      sourceStageId := "main.ct6"
      targetStageId := "main.ct9"
      kind := .registeredTransition
      label := "active-ledger transition"
      description := "The registered CT6 active-ledger transition constructs and executes CT9's parity profile through the semantic adapter."
      transitionProfileId? := some "CT6.residual.activeLedger->CT9"
      evidenceDeclarations := [`EvenCycleExample.ct6ToCT9ItemAdapter]
    },
    {
      linkId := "main.ct9-certificate"
      sourceStageId := "main.ct9"
      targetStageId := "main.certificate"
      kind := .frameworkComposition
      label := "overloaded parity fibre"
      description := "The graph profile consumes CT9's overloaded pair and constructs the even-cycle certificate."
      evidenceDeclarations := [`EvenCycleExample.sameParityEndpointPositions]
    },
    {
      linkId := "main.certificate-ct1"
      sourceStageId := "main.certificate"
      targetStageId := "main.ct1"
      kind := .validation
      label := "validated by CT1"
      description := "The certificate is passed directly to the reusable CT1 target encoding."
    },
    {
      linkId := "main.certificate-theorem"
      sourceStageId := "main.certificate"
      targetStageId := "main.theorem"
      kind := .proofData
      label := "witnesses target"
      description := "The certified chord cycle witnesses the public target."
      evidenceDeclarations := [`EvenCycleExample.hasEvenCycle_of_minDegree_three]
    },
    {
      linkId := "main.ct1-theorem"
      sourceStageId := "main.ct1"
      targetStageId := "main.theorem"
      kind := .validation
      label := "target confirmed"
      description := "The exact CT1 run independently confirms the generated certificate."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "even-cycle"
  title := "Even cycle"
  summary :=
    "A complete minimum-degree-three proof that selects one graph profile and delegates CT6, the registered CT6→CT9 route, certificate construction, and CT1 validation to the framework."
  proofStatus := .complete
  workflows := [mainWorkflow]
  interfaceBindings := [
    {
      bindingId := "main.profile"
      stageId := "main.ct6"
      tacticId := "CT6"
      role := "problem profile selection"
      description := "The application selects the canonical even-cycle endpoint-parity profile; no raw CT capability is reimplemented."
      problemDeclaration := `EvenCycleExample.endpointParityProfile
      frameworkDeclaration :=
        `StructuralExhaustion.Graph.EndpointParityCycle.Profile.evenCycle
    },
    {
      bindingId := "main.ct9-adapter"
      stageId := "main.ct9"
      tacticId := "CT9"
      role := "transition adapter"
      description := "The selected profile exposes the endpoint-neighbor semantics consumed by the registered transition."
      problemDeclaration := `EvenCycleExample.ct6ToCT9ItemAdapter
      frameworkDeclaration := `StructuralExhaustion.Routes.CT6ToCT9.transition
    },
    {
      bindingId := "main.ct1-target"
      stageId := "main.ct1"
      tacticId := "CT1"
      role := "target encoding"
      description := "The selected graph profile supplies the even-cycle target encoding used by CT1."
      problemDeclaration := `EvenCycleExample.ct1TargetBridge
      frameworkDeclaration := `StructuralExhaustion.CT1.run
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `EvenCycleExample `EvenCycleExample.WebExport.descriptor descriptor

end EvenCycleExample.WebExport
