import EvenCycleExample.CT1Instance
import StructuralExhaustion.Graph.MinimumDegreeCycleRouted
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace EvenCycleExample.CT2Audit

open StructuralExhaustion

universe u


/-! The graph profile generates the complete deletion-only CT2 API. -/

abbrev pieces (V : Type u) := (staticInput V).ct2Pieces

abbrev capability (V : Type u) := (staticInput V).ct2Capability

abbrev deletionClosureRule (V : Type u) :=
  (staticInput V).ct2DeletionRule

abbrev routedProfile (V : Type u) :=
  (staticInput V).cycleDeletionProfile

abbrev ct1Input {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (routedProfile V).input ctx

abbrev ct1AvoidingRun {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (routedProfile V).runAvoiding ctx

abbrev ct1AvoidingSource {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :
    Routes.CT1ToCT2.PackedAvoiding (ct1Spec V) (ct1Input ctx) :=
  (routedProfile V).avoidingSource ctx

abbrev canonicalMinimality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :
    Core.MinimalityKernel (problem V) (CT1.Target (ct1Spec V))
      (ct1Input ctx).context :=
  (routedProfile V).targetMinimality ctx

abbrev canonicalDeletionRule (V : Type u) :
    CT2.LocalDeletionClosureRule (Target := CT1.Target (ct1Spec V))
      (capability V) :=
  (routedProfile V).routedClosure

abbrev ct1Ledger {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (routedProfile V).sourceLedger ctx

abbrev currentAvoiding {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (routedProfile V).currentAvoiding ctx

abbrev localTransition {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (routedProfile V).transition ctx

abbrev localLedgerTransition {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :=
  (localTransition ctx).onLedger (currentAvoiding ctx)

theorem localTransition_not_enabled {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :
    ∀ stage : (localLedgerTransition ctx).EnabledStage (ct1Ledger ctx),
      (routedProfile V).outcome ctx ≠ .enabled stage :=
  (routedProfile V).transition_not_enabled ctx

theorem localTransition_profile_id {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V))) :
    (localTransition ctx).profileId =
      Routes.CT1ToCT2.LocalDeletion.transitionId := rfl

/-- CT2 derives the heavy-edge invariant; it is not an authored obligation. -/
theorem degree_three_endpoint {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V)))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 :=
  (staticInput V).routedDart_has_tight_endpoint
    (evenCycleEncoding V) ctx dart

/-- Adjacency-facing form of the same CT2 invariant. -/
theorem invariant_I1 {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V)))
    {source target : V} (adjacent : ctx.G.graph.Adj source target) :
    ctx.G.degree source = 3 ∨ ctx.G.degree target = 3 :=
  degree_three_endpoint ctx ⟨(source, target), adjacent⟩

/-- Exact deletion-C2 run for any explicitly exhibited heavy dart. -/
abbrev heavyDartRun {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V)))
    (dart : ctx.G.graph.Dart)
    (heavy : 4 ≤ ctx.G.degree dart.fst ∧
      4 ≤ ctx.G.degree dart.snd) :=
  (staticInput V).heavyDartRun ctx dart heavy

/-! ## Lexicographic proper-subgraph CT2 transfer -/

/-- The standard even-cycle problem on the varying-vertex packed ambient. -/
def packedStaticInput : Graph.PackedMinimumDegreeCycle.StaticInput where
  minimumDegree := 3
  LengthOK := fun length => length % 2 = 0

/-- Certificate-driven CT2 execution for an arbitrary proper subgraph. -/
def properCoreCT2Run
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :=
  packedStaticInput.properSubgraphCT2Run ctx subgraph minimumDegreeThree

theorem properCoreCT2Run_terminal
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :
    (properCoreCT2Run ctx subgraph minimumDegreeThree).terminal =
      .deletionC2 := rfl

theorem properCoreCT2Run_trace
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :
    (properCoreCT2Run ctx subgraph minimumDegreeThree).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := rfl

theorem properCoreCT2Run_checks
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :
    (properCoreCT2Run ctx subgraph minimumDegreeThree).checks = 1 := rfl

/-- In a lexicographically minimal hypothetical minimum-degree-three graph
without an even cycle, every proper subgraph has minimum degree at most two. -/
theorem properSubgraph_minDegree_le_two
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G) :
    subgraph.value.object.minDegree ≤ 2 := by
  have noCore := packedStaticInput.noProperCore ctx subgraph
  change ¬ 3 ≤ subgraph.value.object.minDegree at noCore
  omega

/-- Natural-number well-ordering selects the packed minimal context and
executes the edge-rooted CT1, local dart-deletion CT2, and proper-subgraph CT2
prefix without enumerating finite graphs. -/
theorem exists_noProperCorePrefix {V : Type u}
    (object : Graph.FiniteObject V) (baseline : Baseline object)
    (avoids : ¬ HasEvenCycle object) :
    ∃ ctx : Core.MinimalCounterexampleContext
        (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
          packedStaticInput)
        (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
          packedStaticInput),
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput).rank ctx.G ≤
          (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
            packedStaticInput).rank
            (Graph.PackedFiniteObject.pack object) ∧
        packedStaticInput.EdgeRootedNoProperCorePrefix ctx :=
  packedStaticInput.exists_edgeRootedNoProperCorePrefix
    object baseline avoids

end EvenCycleExample.CT2Audit
