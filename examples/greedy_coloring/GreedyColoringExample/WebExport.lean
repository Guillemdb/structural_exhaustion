import GreedyColoringExample
import StructuralExhaustion.Canonical.ExampleExport

namespace GreedyColoringExample.WebExport

open StructuralExhaustion.Canonical

private def coloringWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "coloring"
  title := "Deterministic greedy coloring"
  purpose :=
    "Expose the CT12 schedule audit, repeated CT4 color selection, constructed coloring, and final CT1 validation."
  completion := .complete
  stages := [
    {
      stageId := "coloring.problem"
      title := "Maximum-degree coloring target"
      summary := "The target uses Mathlib's graph-coloring API with exactly maximum degree plus one available colors."
      kind := .problem
      primaryDeclaration := `GreedyColoringExample.Target
      evidenceDeclarations := [`GreedyColoringExample.coloring]
    },
    {
      stageId := "coloring.ct12"
      title := "CT12 vertex-peeling audit"
      summary := "CT12 certifies that the declared finite vertex order is peeled to exhaustion."
      kind := .tactic
      tacticId? := some "CT12"
      primaryDeclaration := `GreedyColoringExample.ct12Run
      evidenceDeclarations := [
        `GreedyColoringExample.ConcreteK4.ct12_terminal_exhausted,
        `GreedyColoringExample.ConcreteK4.ct12_iterations_exact
      ]
    },
    {
      stageId := "coloring.ct4"
      title := "CT4 missing-color steps"
      summary := "Each reverse-fold step uses CT4 functional cardinality to choose a color absent from all later neighbors."
      kind := .tactic
      tacticId? := some "CT4"
      primaryDeclaration := `StructuralExhaustion.Graph.GreedyColoring.stepRun
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.GreedyColoring.step_terminal_missing,
        `StructuralExhaustion.Graph.GreedyColoring.selectedColor_available,
        `GreedyColoringExample.ConcreteK4.ct4_terminal_missing,
        `GreedyColoringExample.ConcreteK4.ct4_trace_exact
      ]
    },
    {
      stageId := "coloring.certificate"
      title := "Greedy coloring certificate"
      summary := "The reverse fold assembles all CT4 choices into a complete proper Mathlib coloring."
      kind := .certificate
      primaryDeclaration := `GreedyColoringExample.coloring
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.GreedyColoring.maxDegreeColoring,
        `GreedyColoringExample.ConcreteK4.coloring_values,
        `GreedyColoringExample.ConcreteK4.coloring_is_proper
      ]
    },
    {
      stageId := "coloring.ct1"
      title := "CT1 coloring validation"
      summary := "CT1 validates the completed proper coloring against the finite target encoding."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `GreedyColoringExample.ct1Run
      evidenceDeclarations := [
        `GreedyColoringExample.ConcreteK4.ct1_terminal_c1,
        `GreedyColoringExample.ConcreteK4.ct1_trace_exact
      ]
    },
    {
      stageId := "coloring.theorem"
      title := "Maximum-degree coloring theorem"
      summary := "Every explicitly finite simple graph is colorable with one more color than its maximum degree."
      kind := .theorem
      primaryDeclaration := `GreedyColoringExample.maxDegreeSucc_colorable
      evidenceDeclarations := [`StructuralExhaustion.Graph.GreedyColoring.colorable_maxDegree_succ]
    }
  ]
  links := [
    {
      linkId := "coloring.problem-ct12"
      sourceStageId := "coloring.problem"
      targetStageId := "coloring.ct12"
      kind := .sharedProblem
      label := "audits vertex order"
      description := "The finite graph's declared vertex enumeration is the schedule inspected by CT12."
    },
    {
      linkId := "coloring.ct12-ct4"
      sourceStageId := "coloring.ct12"
      targetStageId := "coloring.ct4"
      kind := .scheduleAudit
      label := "certifies schedule"
      description := "CT12 audits the same vertex order used by the fold; this is orchestration, not a registered residual route."
      automationDeclarations := [
        `StructuralExhaustion.Graph.GreedyColoring.colorOrder,
        `StructuralExhaustion.Graph.GreedyColoring.peelingRun
      ]
      evidenceDeclarations := [`StructuralExhaustion.Graph.GreedyColoring.peeling_terminal_exhausted]
    },
    {
      linkId := "coloring.ct4-certificate"
      sourceStageId := "coloring.ct4"
      targetStageId := "coloring.certificate"
      kind := .frameworkComposition
      label := "repeated reverse fold"
      description := "The framework-owned reverse fold repeatedly invokes CT4 and inserts each selected color into the partial coloring."
      evidenceDeclarations := [`StructuralExhaustion.Graph.GreedyColoring.colorOrder]
    },
    {
      linkId := "coloring.certificate-ct1"
      sourceStageId := "coloring.certificate"
      targetStageId := "coloring.ct1"
      kind := .validation
      label := "validated by CT1"
      description := "CT1 checks the proper coloring after it has been constructed by the CT4 fold."
    },
    {
      linkId := "coloring.certificate-theorem"
      sourceStageId := "coloring.certificate"
      targetStageId := "coloring.theorem"
      kind := .proofData
      label := "witnesses colorability"
      description := "The complete coloring is the witness required by Mathlib's Colorable predicate."
      evidenceDeclarations := [`StructuralExhaustion.Graph.GreedyColoring.colorable_maxDegree_succ]
    },
    {
      linkId := "coloring.ct1-theorem"
      sourceStageId := "coloring.ct1"
      targetStageId := "coloring.theorem"
      kind := .validation
      label := "target confirmed"
      description := "The CT1 success run independently confirms the generated certificate realizes the target."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "greedy-coloring"
  title := "Greedy coloring"
  summary :=
    "A complete maximum-degree coloring construction combining a CT12 schedule audit, repeated CT4 choices, and CT1 certificate validation."
  proofStatus := .complete
  workflows := [coloringWorkflow]
  interfaceBindings := [
    {
      bindingId := "coloring.ct12-list"
      stageId := "coloring.ct12"
      tacticId := "CT12"
      role := "peeling schedule"
      description := "The graph's ordered vertex list is passed to the reusable list-peeling CT12 profile."
      problemDeclaration := `StructuralExhaustion.Graph.GreedyColoring.peelingRun
      frameworkDeclaration := `StructuralExhaustion.CT12.run
    },
    {
      bindingId := "coloring.ct4-profile"
      stageId := "coloring.ct4"
      tacticId := "CT4"
      role := "functional-cardinality profile"
      description := "The step profile maps used colors to later-neighbor payer slots and supplies CT4's functional witness."
      problemDeclaration := `StructuralExhaustion.Graph.GreedyColoring.stepProfile
      frameworkDeclaration := `StructuralExhaustion.CT4.run
    },
    {
      bindingId := "coloring.ct1-encoding"
      stageId := "coloring.ct1"
      tacticId := "CT1"
      role := "target encoding"
      description := "The coloring target encoding exposes the generated coloring and properness proof to CT1."
      problemDeclaration := `StructuralExhaustion.Graph.GreedyColoring.ct1Encoding
      frameworkDeclaration := `StructuralExhaustion.CT1.run
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `GreedyColoringExample `GreedyColoringExample.WebExport.descriptor descriptor

end GreedyColoringExample.WebExport
