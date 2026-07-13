import Erdos64EG
import StructuralExhaustion.Canonical.ExampleExport

namespace Erdos64EG.WebExport

open StructuralExhaustion.Canonical

private def proofSliceWorkflow : ExampleWorkflowDescriptor := {
  workflowId := "proof-slice"
  title := "Current Erdős 64 proof slice"
  purpose :=
    "Inspect the faithful statement boundary and the parallel CT1, CT2, and CT3 interfaces without implying a completed global proof."
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
      title := "K₄ power-of-two certificate"
      summary := "The only closed fixture supplies an explicit four-cycle and verifies the minimum-degree baseline."
      kind := .fixture
      primaryDeclaration := `Erdos64EG.Tests.k4Cycle
      evidenceDeclarations := [
        `Erdos64EG.Tests.k4_baseline,
        `Erdos64EG.Tests.fourCycleWalk_isCycle,
        `Erdos64EG.Tests.fourCycleWalk_powerOfTwo
      ]
    },
    {
      stageId := "proof-slice.ct1"
      title := "CT1 local certificate validation"
      summary := "Given an explicit power-of-two cycle, CT1 reaches its certified success result without enumerating walks."
      kind := .tactic
      tacticId? := some "CT1"
      primaryDeclaration := `Erdos64EG.Internal.runCT1
      evidenceDeclarations := [`Erdos64EG.Tests.k4CT1Run]
    },
    {
      stageId := "proof-slice.ct2"
      title := "CT2 deletion criticality"
      summary := "In a hypothetical minimal counterexample, deletion-only CT2 forces every edge to have a degree-three endpoint."
      kind := .tactic
      tacticId? := some "CT2"
      primaryDeclaration := `Erdos64EG.Internal.heavyDartRun
      evidenceDeclarations := [`Erdos64EG.Internal.deletionCriticality]
    },
    {
      stageId := "proof-slice.ct3"
      title := "CT3 boundaried compression interface"
      summary := "A manuscript-supplied finite response contract can be executed and audited by CT3, but no concrete global contract is supplied here."
      kind := .tactic
      tacticId? := some "CT3"
      primaryDeclaration := `Erdos64EG.Internal.runCT3
      evidenceDeclarations := [
        `Erdos64EG.Internal.targetResponse_eq_true_iff,
        `Erdos64EG.Internal.sameResponse_target_iff,
        `Erdos64EG.Internal.runCT3_checkLimit,
        `Erdos64EG.Internal.runCT3_verified,
        `Erdos64EG.Internal.runCT3_traceValid,
        `Erdos64EG.Internal.runCT3_total
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
      description := "The internal target is proved equivalent to the exact conclusion of the official formulation; this is not a proof of that conclusion."
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
      label := "validate explicit cycle"
      description := "CT1 validates the supplied K₄ certificate only; it does not discover a cycle in arbitrary graphs."
    },
    {
      linkId := "proof-slice.internal-ct2"
      sourceStageId := "proof-slice.internal"
      targetStageId := "proof-slice.ct2"
      kind := .sharedProblem
      label := "deletion-critical surface"
      description := "The internal profile generates CT2's deletion capability for a hypothetical minimal counterexample."
    },
    {
      linkId := "proof-slice.internal-ct3"
      sourceStageId := "proof-slice.internal"
      targetStageId := "proof-slice.ct3"
      kind := .sharedProblem
      label := "compression surface"
      description := "CT3 shares the internal target but remains conditional on a concrete boundaried response contract."
    },
    {
      linkId := "proof-slice.ct2-ct3"
      sourceStageId := "proof-slice.ct2"
      targetStageId := "proof-slice.ct3"
      kind := .sharedProblem
      label := "parallel proof slices"
      description := "CT2 and CT3 expose compatible problem surfaces; no registered route or composed execution between them is claimed."
    }
  ]
}

def descriptor : ExampleDescriptor := {
  exampleId := "erdos-64"
  title := "Erdős Problem 64"
  summary :=
    "A partial proof slice with a faithful official-statement bridge, one concrete CT1 validation, CT2 deletion criticality, and a conditional CT3 compression interface."
  proofStatus := .partialProof
  workflows := [proofSliceWorkflow]
  interfaceBindings := [
    {
      bindingId := "proof-slice.ct1-target"
      stageId := "proof-slice.ct1"
      tacticId := "CT1"
      role := "power-of-two target encoding"
      description := "The minimum-degree-cycle profile translates an explicit power-of-two cycle into CT1's target realization interface."
      problemDeclaration := `Erdos64EG.Internal.ct1TargetBridge
      frameworkDeclaration := `StructuralExhaustion.CT1.run
    },
    {
      bindingId := "proof-slice.ct2-deletion"
      stageId := "proof-slice.ct2"
      tacticId := "CT2"
      role := "single-dart deletion capability"
      description := "The generated capability supplies graph deletion, rank decrease, baseline preservation, and target transport to CT2."
      problemDeclaration := `Erdos64EG.Internal.ct2Capability
      frameworkDeclaration := `StructuralExhaustion.CT2.run
    },
    {
      bindingId := "proof-slice.ct3-contract"
      stageId := "proof-slice.ct3"
      tacticId := "CT3"
      role := "boundaried response contract"
      description := "A concrete proof must instantiate the piece, context, response, replacement, and polynomial-work fields consumed by CT3."
      problemDeclaration := `Erdos64EG.Internal.BoundariedCompressionContract
      frameworkDeclaration := `StructuralExhaustion.CT3.run
    }
  ]
}

run_cmd StructuralExhaustion.Canonical.ExampleExport.exportExample `Erdos64EG `Erdos64EG.WebExport.descriptor descriptor

end Erdos64EG.WebExport
