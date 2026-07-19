import StructuralExhaustion.Graph.BridgeContraction
import StructuralExhaustion.Graph.EdgeRootedReturn
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Graph.PackedMinimumDegreeCycle

open StructuralExhaustion

universe u

/-!
# CT2 bridge-contraction reduction

This module connects the graph-native bridge contraction to CT2's generic
certified-reduction runner.  A hypothetical bridge supplies the reduction
trigger; all rank, baseline, and target-transport obligations are discharged
here from graph theorems.  The runner performs exactly one certificate check
and enumerates no graph family.
-/

namespace StaticInput

/-- Packed smaller object obtained by contracting one dart. -/
def bridgeContraction (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart) : PackedFiniteObject.{u} :=
  PackedFiniteObject.pack
    (BridgeContraction.finiteObject ctx.G.object dart.fst dart.snd)

/-- Complete CT2 reduction input derived from a genuine bridge. -/
def bridgeCT2Input (input : StaticInput) (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    CT2.CertifiedReductionInput ctx where
  reduction := {
    value := input.bridgeContraction ctx dart
    decreases := PackedFiniteObject.lexRank_lt_of_vertexCount_lt
      (BridgeContraction.vertexCount_lt ctx.G.object dart.fst dart.snd)
  }
  reducedBaseline :=
    BridgeContraction.preserves_minDegree ctx.G.object dart bridge
      input.minimumDegree minimumDegreeAtLeastTwo ctx.baseline
  targetMonotone :=
    BridgeContraction.finiteObject_targetMonotone ctx.G.object dart bridge

/-- Canonical constant-work CT2 execution for a hypothetical bridge. -/
def bridgeCT2Run (input : StaticInput) (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :=
  CT2.runCertifiedReduction ctx
    (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge)

/-- A lexicographically minimal counterexample of minimum degree at least two
has no bridge. -/
theorem not_isBridge (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart) :
    ¬ctx.G.object.graph.IsBridge dart.edge := by
  intro bridge
  exact (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).verified

theorem bridgeCT2Run_terminal (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).terminal =
      .deletionC2 := rfl

theorem bridgeCT2Run_trace (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := rfl

theorem bridgeCT2Run_total (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    ∃ run : CT2.CertifiedReductionRun ctx
        (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge),
      run.terminal = .deletionC2 ∧
        run.trace = [.entry, .deletionDecision, .deletionC2Terminal] :=
  CT2.runCertifiedReduction_total ctx
    (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge)

theorem bridgeCT2Run_checks (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.object.graph.Dart)
    (bridge : ctx.G.object.graph.IsBridge dart.edge) :
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).checks = 1 := rfl

/-- Framework-owned CT2 output for the bridge-contraction stage. -/
structure BridgeReductionStage (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  bridgeless : ∀ dart : ctx.G.object.graph.Dart,
    ¬ctx.G.object.graph.IsBridge dart.edge
  terminal : ∀ dart (bridge : ctx.G.object.graph.IsBridge dart.edge),
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).terminal =
      .deletionC2
  trace : ∀ dart (bridge : ctx.G.object.graph.IsBridge dart.edge),
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).trace =
      [.entry, .deletionDecision, .deletionC2Terminal]
  total : ∀ dart (bridge : ctx.G.object.graph.IsBridge dart.edge),
    ∃ run : CT2.CertifiedReductionRun ctx
        (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge),
      run.terminal = .deletionC2 ∧
        run.trace = [.entry, .deletionDecision, .deletionC2Terminal]
  checks : ∀ dart (bridge : ctx.G.object.graph.IsBridge dart.edge),
    (input.bridgeCT2Run minimumDegreeAtLeastTwo ctx dart bridge).checks = 1

/-- Proof-indexed local universe for the bridge-contraction audit.  This is a
dependent function index, not an enumeration of darts or graphs. -/
abbrev BridgeReductionIndex (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :=
  { dart : ctx.G.object.graph.Dart //
    ctx.G.object.graph.IsBridge dart.edge }

/-- One public certificate-driven CT2 execution for every hypothetical
bridge.  Packaging these executions pointwise performs no ambient scan: an
execution is produced only when its dart and bridge proof are supplied. -/
def bridgeReductionFamily (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    Core.Routing.PointwiseExecutableFamily .ct2 where
  Index := input.BridgeReductionIndex ctx
  entry := fun _index =>
    CT2.certifiedReductionExecutableInterface input.problem input.Target
  context := fun _index => ctx
  trigger := fun index =>
    input.bridgeCT2Input minimumDegreeAtLeastTwo ctx index.1 index.2

/-- Reconstruct the graph-level bridgeless certificate from the literal
pointwise CT2 executions returned by an accumulated transition. -/
def bridgeReductionStageOfExecutions (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (runs : (index : input.BridgeReductionIndex ctx) →
      CT2.CertifiedReductionRun ctx
        (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx index.1 index.2)) :
    input.BridgeReductionStage minimumDegreeAtLeastTwo ctx where
  bridgeless := by
    intro dart bridge
    exact (runs ⟨dart, bridge⟩).verified
  terminal := by
    intro dart bridge
    exact CT2.runCertifiedReduction_terminal ctx
      (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge)
  trace := by
    intro dart bridge
    exact CT2.runCertifiedReduction_trace ctx
      (input.bridgeCT2Input minimumDegreeAtLeastTwo ctx dart bridge)
  total := by
    intro dart bridge
    exact input.bridgeCT2Run_total minimumDegreeAtLeastTwo ctx dart bridge
  checks := by
    intro dart bridge
    exact input.bridgeCT2Run_checks minimumDegreeAtLeastTwo ctx dart bridge

def bridgeReductionStage (input : StaticInput)
    (minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    input.BridgeReductionStage minimumDegreeAtLeastTwo ctx where
  bridgeless := input.not_isBridge minimumDegreeAtLeastTwo ctx
  terminal := input.bridgeCT2Run_terminal minimumDegreeAtLeastTwo ctx
  trace := input.bridgeCT2Run_trace minimumDegreeAtLeastTwo ctx
  total := input.bridgeCT2Run_total minimumDegreeAtLeastTwo ctx
  checks := input.bridgeCT2Run_checks minimumDegreeAtLeastTwo ctx

/-- Framework-native CT2-to-return transition.  The CT2 stage proves the
dart non-bridging; Mathlib then supplies a simple deleted-edge return by
proof-level choice, without a walk search. -/
noncomputable def BridgeReductionStage.dartReturn
    {input : StaticInput} {minimumDegreeAtLeastTwo : 2 ≤ input.minimumDegree}
    {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
    (stage : input.BridgeReductionStage minimumDegreeAtLeastTwo ctx)
    (dart : ctx.G.object.graph.Dart) : DartReturn ctx.G.object.graph dart :=
  DartReturn.ofNotBridge (stage.bridgeless dart)

end StaticInput

end StructuralExhaustion.Graph.PackedMinimumDegreeCycle
