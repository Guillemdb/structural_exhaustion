import Erdos64EG.CT1
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT2: single-dart deletion criticality

The Mathlib graph profile owns dart enumeration, endpoint-slack testing,
single-edge deletion, exact rank decrease, baseline preservation, target
transport, and the deletion-only CT2 runner.  This file routes CT1's exact
avoiding residual into that local CT2 profile and exports the resulting
deletion-critical prefix.
-/

abbrev ct2Capability (V : Type u) := (staticInput V).ct2Capability
abbrev ct2DeletionRule (V : Type u) := (staticInput V).ct2DeletionRule
abbrev routedProfile (V : Type u) :=
  (staticInput V).edgeRootedDeletionProfile

/-! ## Typed CT1-to-local-CT2 composition -/

/-- The certified CT1 avoiding execution on a public minimal-counterexample
context. -/
def minimalCT1Run {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (routedProfile V).runAvoiding ctx

/-- Extract the exact semantic residual produced by the preceding CT1 run. -/
def ct1AvoidingSource {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    Routes.CT1ToCT2.PackedAvoiding (ct1Spec V)
      (ct1Input ctx.G ctx.baseline) :=
  (routedProfile V).avoidingSource ctx

/-- Transport the public minimality theorem through CT1's exact target
bridge. -/
def ct1Minimality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    Core.MinimalityKernel (problem V) (CT1.Target (ct1Spec V))
      (ct1Input ctx.G ctx.baseline).context :=
  (routedProfile V).targetMinimality ctx

/-- Transport the graph profile's local deletion rule through the same CT1
target bridge. -/
def routedDeletionRule (V : Type u) :
    CT2.LocalDeletionClosureRule (Target := CT1.Target (ct1Spec V))
      (ct2Capability V) :=
  (routedProfile V).routedClosure

abbrev ct1Ledger {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (routedProfile V).sourceLedger ctx

abbrev currentAvoiding {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (routedProfile V).currentAvoiding ctx

abbrev localTransition {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (routedProfile V).transition ctx

abbrev routedContext {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (routedProfile V).routedContext ctx

/-- An enabled heavy-dart transition would execute CT2's deletion-C2
contradiction, so the full CT1 ledger admits no enabled CT2 stage. -/
theorem localTransition_not_enabled {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    ∀ stage : Core.Routing.ResidualStage .ct2
      ((localTransition ctx).OutputLedger
        (currentAvoiding ctx) (ct1Ledger ctx)),
      (routedProfile V).outcome ctx ≠ .enabled stage :=
  (routedProfile V).transition_not_enabled ctx

/-- In a minimal counterexample, every actual edge has a degree-three
endpoint. -/
theorem deletionCriticality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 := by
  simpa [staticInput] using
    (staticInput V).routedDart_has_tight_endpoint
      (staticInput V).edgeRootedEncoding ctx dart

/-- No two vertices of degree at least four are adjacent. -/
theorem highDegree_independent {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    {left right : V}
    (leftHeavy : 4 ≤ ctx.G.degree left)
    (rightHeavy : 4 ≤ ctx.G.degree right) :
    ¬ ctx.G.graph.Adj left right := by
  simpa [staticInput] using
    (staticInput V).routedHighDegree_independent
      (staticInput V).edgeRootedEncoding ctx leftHeavy rightHeavy

/-- Exact deletion-C2 execution for an explicitly supplied heavy dart. -/
def heavyDartRun {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart)
    (heavy : 4 ≤ ctx.G.degree dart.fst ∧
      4 ≤ ctx.G.degree dart.snd) :
    CT2.LocalDeletionRun (ct2Capability V) ctx
      ⟨⟨dart, heavy, trivial⟩⟩ :=
  (staticInput V).heavyDartRun ctx dart heavy

/-! ## Completed verified prefix -/

/-- The exact outputs of the composed Mersenne CT1 and local-deletion CT2
prefix on a minimal counterexample. -/
abbrev VerifiedCT1CT2Prefix {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  (staticInput V).EdgeRootedDeletionPrefix ctx

def verifiedCT1CT2Prefix {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    VerifiedCT1CT2Prefix ctx :=
  (staticInput V).edgeRootedDeletionPrefix ctx

/-- Starting from any supplied counterexample graph on the declared vertex
type, natural-number well-ordering selects an edge-rank-minimal representative
and the framework executes the complete verified CT1-to-CT2 prefix on it.  No
ambient graph universe is enumerated. -/
theorem exists_verifiedCT1CT2Prefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext (problem V) (@Target V),
      (problem V).rank ctx.G ≤ (problem V).rank object ∧
        VerifiedCT1CT2Prefix ctx :=
  (staticInput V).exists_edgeRootedDeletionPrefix
    (fun _object => ()) object baseline avoids

/-! ## Manuscript node [8]: no proper core -/

/-- The Mersenne-cycle problem on the framework's varying-vertex packed graph
ambient. -/
def packedStaticInput : Graph.PackedMinimumDegreeCycle.StaticInput where
  minimumDegree := 3
  LengthOK := PowerOfTwoLength

/-- Exact output of node [8], retaining the preceding edge-rooted CT1 and
local-deletion CT2 outputs on the selected graph. -/
abbrev VerifiedNoProperCorePrefix
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput)) :=
  packedStaticInput.EdgeRootedNoProperCorePrefix ctx

/-- The fixed-vertex component of node [8]'s output is exactly the previously
verified Erdős CT1/CT2 prefix. -/
theorem noProperCorePrefix_previous
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (verified : VerifiedNoProperCorePrefix ctx) :
    VerifiedCT1CT2Prefix (packedStaticInput.fixedContext ctx) := by
  change (packedStaticInput.fixed ctx.G.Vertex).EdgeRootedDeletionPrefix
    (packedStaticInput.fixedContext ctx)
  exact verified.fixedPrefix

/-- Public CT2 execution for one explicitly supplied proper subgraph retaining
minimum degree three. -/
def properCoreCT2Run
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :=
  packedStaticInput.properSubgraphCT2Run ctx subgraph minimumDegreeThree

/-- Every proper subgraph of the selected counterexample has minimum degree at
most two, exactly as in manuscript Lemma `lem:no-proper-core`. -/
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

/-- Exact CT2 terminal for the contradictory proper-core branch. -/
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

/-- Exact typed CT2 trace for the contradictory proper-core branch. -/
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

/-- Node [8] uses exactly one certificate check. -/
theorem properCoreCT2Run_checks
    (ctx : Core.MinimalCounterexampleContext
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput)
      (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
        packedStaticInput))
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
    (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree) :
    (properCoreCT2Run ctx subgraph minimumDegreeThree).checks = 1 := rfl

/-- Starting with the official internal counterexample data, select the same
lexicographically minimal graph used by node [8] and execute the complete
verified CT1/CT2 prefix through the no-proper-core conclusion. -/
theorem exists_verifiedNoProperCorePrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
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
        VerifiedNoProperCorePrefix ctx := by
  exact packedStaticInput.exists_edgeRootedNoProperCorePrefix
    object baseline avoids

end Erdos64EG.Internal
