import MantelExample
import StructuralExhaustion.Canonical.ExampleExport

namespace MantelExample.WebExport

open StructuralExhaustion.Canonical

private def proofWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "proof"
  title := "Mantel bound by CT11 localization"
  purpose :=
    "Follow the contradiction proof from a failed numerical bound through CT11 localization to the triangle-free degree bound."
  completion := .complete
  stages := [
    {
      stageId := "proof.problem"
      title := "Triangle-free Mantel target"
      summary := "The external problem supplies a finite graph, a triangle-free hypothesis, and the standard quarter-square edge bound."
      kind := .problem
      primaryDeclaration := `MantelExample.Target
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.degree_add_degree_le_card_of_triangleFree]
    },
    {
      stageId := "proof.budget"
      title := "Negative global dart budget"
      summary := "Negating the Mantel inequality makes the exact sum of local endpoint-degree budgets strictly negative."
      kind := .adapter
      primaryDeclaration := `StructuralExhaustion.Graph.Mantel.deficit_of_mantel_violation
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.Mantel.sum_localBudget_eq,
        `StructuralExhaustion.Graph.Mantel.four_mul_edgeCount_sq_le_card_mul_degreeSquareSum
      ]
    },
    {
      stageId := "proof.ct11"
      title := "CT11 deficit localization"
      summary := "CT11 chooses an oriented edge whose local endpoint-degree budget is negative."
      kind := .tactic
      tacticId? := some "CT11"
      primaryDeclaration := `MantelExample.ct11Run
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.run_terminal_localized]
    },
    {
      stageId := "proof.residual"
      title := "Offending dart residual"
      summary := "The localized residual states that the selected edge's endpoint degrees sum to more than the vertex count."
      kind := .certificate
      primaryDeclaration := `StructuralExhaustion.Graph.Mantel.offendingResidual
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.offending_degree_sum_gt]
    },
    {
      stageId := "proof.theorem"
      title := "Mantel theorem"
      summary := "Triangle-freeness bounds the same endpoint-degree sum from above, contradicting the CT11 residual."
      kind := .theorem
      primaryDeclaration := `MantelExample.mantel
      evidenceDeclarations := [
        `StructuralExhaustion.Graph.Mantel.four_mul_edgeCount_le_card_sq_of_triangleFree,
        `StructuralExhaustion.Graph.Mantel.edgeCount_le_card_sq_div_four_of_triangleFree
      ]
    }
  ]
  links := [
    {
      linkId := "proof.problem-budget"
      sourceStageId := "proof.problem"
      targetStageId := "proof.budget"
      kind := .proofData
      label := "negate target"
      description := "A hypothetical failure of the target is converted, using the degree-sum identity and Cauchy–Schwarz, into a negative total budget."
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.deficit_of_mantel_violation]
    },
    {
      linkId := "proof.budget-ct11"
      sourceStageId := "proof.budget"
      targetStageId := "proof.ct11"
      kind := .frameworkComposition
      label := "instantiate CT11"
      description := "The graph-specific profile supplies dart cells and local budgets to the generic CT11 negative-budget runner."
    },
    {
      linkId := "proof.ct11-residual"
      sourceStageId := "proof.ct11"
      targetStageId := "proof.residual"
      kind := .proofData
      label := "localized deficit"
      description := "CT11's localized terminal exposes the canonical dart and its certified negative local budget."
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.offending_degree_sum_gt]
    },
    {
      linkId := "proof.residual-theorem"
      sourceStageId := "proof.residual"
      targetStageId := "proof.theorem"
      kind := .proofData
      label := "contradicts triangle-freeness"
      description := "The residual's strict lower bound contradicts the neighborhood-disjointness upper bound forced by triangle-freeness."
      evidenceDeclarations := [`StructuralExhaustion.Graph.Mantel.degree_add_degree_le_card_of_triangleFree]
    }
  ]
}

private def k4Workflow : ExampleWorkflowDescriptor := {
  workflowId := "k4-localization"
  title := "K₄ CT11 localization fixture"
  purpose :=
    "Execute and pin CT11 on a graph that violates the numerical bound; K₄ is intentionally not a Mantel-theorem instance."
  completion := .complete
  stages := [
    {
      stageId := "k4-localization.fixture"
      title := "K₄ violating fixture"
      summary := "K₄ supplies a closed proof that the multiplication-form Mantel bound is violated."
      kind := .fixture
      primaryDeclaration := `MantelExample.ConcreteK4.object
      evidenceDeclarations := [`MantelExample.ConcreteK4.violation]
    },
    {
      stageId := "k4-localization.ct11"
      title := "Concrete CT11 execution"
      summary := "The exact run localizes the first offending dart in the declared finite order."
      kind := .tactic
      tacticId? := some "CT11"
      primaryDeclaration := `MantelExample.ConcreteK4.execution
      evidenceDeclarations := [
        `MantelExample.ConcreteK4.terminal_localized,
        `MantelExample.ConcreteK4.trace_exact,
        `MantelExample.ConcreteK4.selected_dart_exact
      ]
    },
    {
      stageId := "k4-localization.audit"
      title := "Localized-run audit"
      summary := "The fixture records the localized terminal, full trace, and selected oriented edge."
      kind := .certificate
      primaryDeclaration := `MantelExample.ConcreteK4.selected_dart_exact
      evidenceDeclarations := [
        `MantelExample.ConcreteK4.terminal_localized,
        `MantelExample.ConcreteK4.trace_exact
      ]
    }
  ]
  links := [
    {
      linkId := "k4-localization.fixture-ct11"
      sourceStageId := "k4-localization.fixture"
      targetStageId := "k4-localization.ct11"
      kind := .frameworkComposition
      label := "run violating input"
      description := "The concrete violation is converted to a negative budget and passed to CT11."
    },
    {
      linkId := "k4-localization.ct11-audit"
      sourceStageId := "k4-localization.ct11"
      targetStageId := "k4-localization.audit"
      kind := .proofData
      label := "pins execution"
      description := "Kernel-checked equalities pin the exact terminal, trace, and selected dart."
      evidenceDeclarations := [`MantelExample.ConcreteK4.trace_exact]
    }
  ]
}

private def c5Workflow : ExampleWorkflowDescriptor := {
  workflowId := "c5-theorem"
  title := "C₅ Mantel-theorem fixture"
  purpose :=
    "Apply the completed theorem to a concrete non-bipartite triangle-free graph, separately from the K₄ machine fixture."
  completion := .complete
  stages := [
    {
      stageId := "c5-theorem.fixture"
      title := "C₅ finite graph"
      summary := "The five-cycle is represented with Mathlib's canonical cycle graph and explicit finite input."
      kind := .fixture
      primaryDeclaration := `MantelExample.ConcreteC5.object
      evidenceDeclarations := [`MantelExample.ConcreteC5.edgeCount_exact]
    },
    {
      stageId := "c5-theorem.triangle-free"
      title := "Triangle-free certificate"
      summary := "A closed finite computation certifies that C₅ contains no three-clique."
      kind := .certificate
      primaryDeclaration := `MantelExample.ConcreteC5.triangleFree
    },
    {
      stageId := "c5-theorem.bound"
      title := "Concrete Mantel bound"
      summary := "The public Mantel theorem consumes the triangle-free certificate and proves the target for C₅."
      kind := .theorem
      primaryDeclaration := `MantelExample.ConcreteC5.mantel_bound
      evidenceDeclarations := [`MantelExample.mantel]
    }
  ]
  links := [
    {
      linkId := "c5-theorem.fixture-certificate"
      sourceStageId := "c5-theorem.fixture"
      targetStageId := "c5-theorem.triangle-free"
      kind := .proofData
      label := "finite check"
      description := "The concrete adjacency decision procedure proves the required triangle-free hypothesis."
    },
    {
      linkId := "c5-theorem.certificate-bound"
      sourceStageId := "c5-theorem.triangle-free"
      targetStageId := "c5-theorem.bound"
      kind := .proofData
      label := "invoke theorem"
      description := "The C₅ certificate instantiates the hypothesis of the completed generic Mantel theorem."
      evidenceDeclarations := [`MantelExample.ConcreteC5.mantel_bound]
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "mantel"
  title := "Mantel's theorem"
  summary :=
    "A complete CT11 localization proof, with K₄ isolated as a machine-only violating fixture and C₅ as a genuine triangle-free theorem instance."
  proofStatus := .complete
  workflows := [proofWorkflow, k4Workflow, c5Workflow]
  interfaceBindings := [
    {
      bindingId := "proof.ct11-profile"
      stageId := "proof.ct11"
      tacticId := "CT11"
      role := "negative-budget profile"
      description := "The Mantel profile chooses graph darts as cells and endpoint-degree deficit as the local CT11 budget."
      problemDeclaration := `StructuralExhaustion.Graph.Mantel.profile
      frameworkDeclaration := `StructuralExhaustion.CT11.run
    },
    {
      bindingId := "k4-localization.ct11-profile"
      stageId := "k4-localization.ct11"
      tacticId := "CT11"
      role := "concrete negative-budget input"
      description := "The K₄ numerical violation instantiates the same graph-specific CT11 profile without claiming triangle-freeness."
      problemDeclaration := `MantelExample.ConcreteK4.execution
      frameworkDeclaration := `StructuralExhaustion.CT11.run
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `MantelExample `MantelExample.WebExport.descriptor descriptor

end MantelExample.WebExport
