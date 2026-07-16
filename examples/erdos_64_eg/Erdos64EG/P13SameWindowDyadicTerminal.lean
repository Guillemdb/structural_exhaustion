import Erdos64EG.P13SameWindowStructuralFrontier
import Erdos64EG.P13ColdGermTerminalRoutes

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Node [159] dyadic terminal consumer for node [155]

This module consumes only a dyadic constructor of the computed node-[159]
same-window frontier.  It rebuilds the existing `ColdDyadicHit` from the
constructor's canonical stub and F1 proof, executes the established
certificate-driven CT1 G1 run, and contradicts target avoidance.

No cycle or target witness is supplied independently of the node-[159]
constructor.  This module does not synchronize or mark manuscript node `[155]`.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

private noncomputable abbrev FrontierProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  InducedPathColdCorridor.firstFailureProfile
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable

private noncomputable abbrev FrontierFirstHit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object) :=
  Core.FiniteSearch.FirstHit
    ((FrontierProfile ctx).stages stub).values
    ((FrontierProfile ctx).Event stub)

/-- One proof that the computed node-[159] output is its dyadic constructor.
All target data are fields of that constructor; no fresh target certificate is
accepted. -/
structure P13ComputedDyadicBranch
    (fork : P13ActualAttachmentColdFork ctx previous window) where
  stub : InducedPathColdCorridor.CubicStub ctx.G.object
  sameWindow : stub.window = selectedConnectorWindowIndex window
  hit : FrontierFirstHit ctx stub
  targetProof : InducedPathColdCorridor.F1
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub hit.value
  target : InducedPathColdCorridor.Producer.TargetHit
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
  targetExact : target = InducedPathColdCorridor.targetHitOfF1
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
    stub hit.value targetProof
  computed : runP13SameWindowStructuralFrontier fork =
    .dyadicTargetHit stub sameWindow hit targetProof target targetExact

namespace P13ComputedDyadicBranch

variable {fork : P13ActualAttachmentColdFork ctx previous window}

/-- Exact node-[155] G1 input reconstructed from the node-[159] constructor.
The path offset is the literal position of the same canonical external stub. -/
noncomputable def coldDyadicHit (branch : P13ComputedDyadicBranch fork) :
    P13ColdGermLedger.ColdDyadicHit packedStaticInput ctx where
  offset := branch.stub.position
  cycle := (InducedPathColdCorridor.targetHitOfF1
    (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
    branch.stub branch.hit.value branch.targetProof).cycle

theorem coldDyadicHit_offset (branch : P13ComputedDyadicBranch fork) :
    branch.coldDyadicHit.offset = branch.stub.position :=
  rfl

theorem stub_window (branch : P13ComputedDyadicBranch fork) :
    branch.stub.window = selectedConnectorWindowIndex window :=
  branch.sameWindow

/-- The G1 input carries exactly the canonical deleted-edge root cycle; no
walk search or replacement certificate is introduced by this adapter. -/
theorem coldDyadicHit_cycle_eq_rootCycle
    (branch : P13ComputedDyadicBranch fork) :
    branch.coldDyadicHit.cycle.walk =
      (p13SelectedWindowCorridorProducer ctx).rootCycle branch.stub :=
  rfl

/-- Execute the existing proof-carrying, one-check CT1 G1 consumer. -/
noncomputable def g1Run (branch : P13ComputedDyadicBranch fork) :=
  P13ColdGermTerminalRoutes.g1Run branch.coldDyadicHit

theorem g1_terminal (branch : P13ComputedDyadicBranch fork) :
    branch.g1Run.result.terminal = .c1 :=
  P13ColdGermTerminalRoutes.g1_terminal branch.coldDyadicHit

theorem g1_trace (branch : P13ComputedDyadicBranch fork) :
    branch.g1Run.result.trace =
      [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  P13ColdGermTerminalRoutes.g1_trace branch.coldDyadicHit

theorem g1_checks (branch : P13ComputedDyadicBranch fork) :
    branch.g1Run.checks = 1 :=
  P13ColdGermTerminalRoutes.g1_checks branch.coldDyadicHit

/-- The exact dyadic node-[159] constructor closes against the inherited
target-avoidance field of the identical minimal-counterexample context. -/
theorem impossible (branch : P13ComputedDyadicBranch fork) : False :=
  P13ColdGermTerminalRoutes.g1_impossible branch.coldDyadicHit

end P13ComputedDyadicBranch

end Erdos64EG.Internal
