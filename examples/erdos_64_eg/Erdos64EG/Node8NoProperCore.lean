import Erdos64EG.Node6MersenneDecision
import Erdos64EG.CT2
import StructuralExhaustion.CT1.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [8]: no proper minimum-degree-three subgraph

The framework continues only node `[6]`'s literal avoiding constructor.  From
that constructor's retained minimal context it executes packed minimality and
CT2 proper-subgraph reduction, appending the resulting no-proper-core
certificate to the same accumulated ledger.  The node-[7] C1 constructor is
preserved unchanged.
-/

/-- The one new node-[8] payload, indexed by the exact node-[6] avoiding run. -/
abbrev Node8Output {V : Type u} {residual : InitialResidual V}
    (node6 : Node6Stage residual)
    (_run : CT1.CertifiedAvoidingRun (ct1Spec V)
      (node6Input node6.previous)) :=
  packedStaticInput.SelectedNoProperCore
    node6.previous.previous.context.G

/-- Stable framework successor type exposed to node `[9]`. -/
abbrev Node8Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (fun current => Node6Stage (V := V) current)
    (fun current node6 =>
      CT1.ResidualRefinement.CertificateAvoidingContinuation
        (mersenneReturnEncoding V) (node6Input node6.previous)
        (@Node8Output V current node6)) residual

/-- Node `[8]` consumes node `[6]`'s literal avoiding branch and invokes the
framework-owned packed-minimality/CT2 executor. -/
noncomputable def node8NoProperCore {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (fun current => Node6Stage (V := V) current)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (fun current => Node8Stage (V := V) current) :=
  CT1.ResidualRefinement.continueCertificateAvoidingUsingStage
    (mersenneReturnEncoding V)
    (fun _residual node5 => node6Input node5)
    (fun _residual node5 _run =>
      Graph.PackedMinimumDegreeCycle.StaticInput.selectNoProperCore
        packedStaticInput node5.previous.context.G
        node5.previous.context.baseline node5.previous.context.avoids)

/-- Continue the live counterexample branch through node `[8]`; all terminal
branches are transported by framework combinators. -/
noncomputable def runInitialThroughNode8 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode6 residual).mapYesStage node8NoProperCore

/-- The node-[8] avoiding successor excludes every proper subgraph retaining
minimum degree three. -/
theorem node8_noProperCore {V : Type u} {residual : InitialResidual V}
    (node6 : Node6Stage residual)
    (run : CT1.CertifiedAvoidingRun (ct1Spec V)
      (node6Input node6.previous))
    (output : Node8Output node6 run) :
    ∀ subgraph : Graph.PackedFiniteObject.ProperSubgraph output.context.G,
      ¬packedStaticInput.problem.Baseline subgraph.value :=
  output.certificate.noProperCore

/-- Each hypothetical proper-core contradiction is the exact CT2 deletion-C2
terminal with its typed trace, total execution, and constant work bound. -/
theorem node8_ct2_certificate {V : Type u}
    {residual : InitialResidual V} (node6 : Node6Stage residual)
    (run : CT1.CertifiedAvoidingRun (ct1Spec V)
      (node6Input node6.previous))
    (output : Node8Output node6 run)
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph output.context.G)
    (baseline : packedStaticInput.problem.Baseline subgraph.value) :
    (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).terminal =
        .deletionC2 ∧
      (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).trace =
        [.entry, .deletionDecision, .deletionC2Terminal] ∧
      (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).checks = 1 :=
  ⟨output.certificate.properCoreTerminal subgraph baseline,
    output.certificate.properCoreTrace subgraph baseline,
    output.certificate.properCoreChecks subgraph baseline⟩

#print axioms runInitialThroughNode8
#print axioms node8_noProperCore
#print axioms node8_ct2_certificate

end Erdos64EG.Internal
