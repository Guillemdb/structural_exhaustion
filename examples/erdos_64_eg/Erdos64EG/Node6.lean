import Erdos64EG.Node5
import Erdos64EG.Shared.CT1
import StructuralExhaustion.CT1.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [6]: exhaustive Mersenne-return CT1 decision

The node consumes the literal node-[5] stage.  CT1 owns the exhaustive
certificate/avoidance split and both terminal-indexed runs; this module only
specializes the input to the selected minimal counterexample.
-/

/-- CT1 input determined by the exact node-[5] predecessor. -/
def node6Input {V : Type u} {residual : InitialResidual V}
    (node5 : Node5Stage residual) :
      CT1.Input (problem node5.previous.context.G.Vertex) :=
  ct1Input (packedStaticInput.fixedContext node5.previous.context).G
    (packedStaticInput.fixedContext node5.previous.context).baseline

/-- The single mathematical CT1 family at node `[6]`.  The packed node-[4]
selection determines its vertex type; the framework instantiates every
dependent field only after retrieving the exact node-[5] predecessor. -/
def node6Family (V : Type u) :
    CT1.ResidualRefinement.DependentCertificateFamily
      (InitialResidual V) (@Node5Stage V) where
  problem := fun _residual node5 =>
    problem node5.previous.context.G.Vertex
  PublicTarget := fun _residual node5 =>
    @Target node5.previous.context.G.Vertex
  encoding := fun _residual node5 =>
    mersenneReturnEncoding node5.previous.context.G.Vertex
  input := fun _residual node5 => node6Input node5

/-- Node `[6]` is the framework-owned CT1 decision on the literal node-[5]
payload. -/
abbrev Node6Stage {V : Type u} (residual : InitialResidual V) :=
  (node6Family V).DecisionSuccessor residual

noncomputable def node6MersenneDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node5Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts) (@Node6Stage V) :=
  (node6Family V).executeUsingStage

/-- Continue only the live counterexample branch; node `[3]` remains untouched. -/
noncomputable def runInitialThroughNode6 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode5 residual).mapYesStage node6MersenneDecision

theorem node6_semantics {V : Type u} {residual : InitialResidual V}
    (stage : Node6Stage residual) :
    match stage.output with
    | .c1 run => CT1.OutcomeClaim run.result.outcome
    | .avoiding run => CT1.OutcomeClaim run.result.outcome := by
  cases stage.output with
  | c1 run => exact run.result.verified
  | avoiding run => exact run.result.verified

theorem node6_trace_exact {V : Type u} {residual : InitialResidual V}
    (stage : Node6Stage residual) :
    match stage.output with
    | .c1 run => run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal]
    | .avoiding run => run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision,
          .avoidingTerminal] := by
  cases stage.output with
  | c1 run => exact run.trace_eq
  | avoiding run => exact run.trace_eq

theorem node6_work_bound {V : Type u} {residual : InitialResidual V}
    (stage : Node6Stage residual) :
    match stage.output with
    | .c1 run => run.checks ≤ 1
    | .avoiding run => run.checks ≤ 1 := by
  cases stage.output with
  | c1 run => exact CT1.certifiedC1Run_checks_le run
  | avoiding run =>
      change run.checks ≤ 1
      rw [run.checks_eq]
      exact Nat.zero_le _

theorem node6_total {V : Type u} {residual : InitialResidual V}
    (node5 : Node5Stage residual) :
    Nonempty ((node6Family V).Decision residual node5) :=
  CT1.ResidualRefinement.decideCertificate_total _ _

#print axioms runInitialThroughNode6
#print axioms node6_semantics
#print axioms node6_trace_exact
#print axioms node6_work_bound
#print axioms node6_total

end Erdos64EG.Internal
