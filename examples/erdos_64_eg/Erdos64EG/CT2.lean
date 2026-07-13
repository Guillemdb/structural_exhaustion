import Erdos64EG.CT1
import StructuralExhaustion.Core.MinimalSelection
import StructuralExhaustion.Routes.CT1ToCT2

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT2: single-dart deletion criticality

The Mathlib graph profile owns dart enumeration, endpoint-slack testing,
single-edge deletion, exact rank decrease, baseline preservation, target
transport, and the deletion-only CT2 runner.  This file only exposes the
problem-named projections used by later EG stages.
-/

abbrev ct2Capability (V : Type u) := (staticInput V).ct2Capability
abbrev ct2DeletionRule (V : Type u) := (staticInput V).ct2DeletionRule

/-! ## Typed CT1-to-local-CT2 composition -/

/-- The certified CT1 avoiding execution on a public minimal-counterexample
context. -/
def minimalCT1Run {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  runAvoidingCT1 ctx.G ctx.baseline ctx.avoids

/-- Extract the exact semantic residual produced by the preceding CT1 run. -/
def ct1AvoidingSource {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    Routes.CT1ToCT2.PackedAvoiding (ct1Spec V)
      (ct1Input ctx.G ctx.baseline) :=
  Routes.CT1ToCT2.PackedAvoiding.ofResult
    (minimalCT1Run ctx).result (minimalCT1Run ctx).terminal_eq

/-- Transport the public minimality theorem through CT1's exact target
bridge. -/
def ct1Minimality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    Core.MinimalityKernel (problem V) (CT1.Target (ct1Spec V))
      (ct1Input ctx.G ctx.baseline).context := by
  intro object smaller baseline
  exact (ct1TargetBridge V).target_of_publicTarget
    (ctx.minimal object smaller baseline)

/-- Transport the graph profile's local deletion rule through the same CT1
target bridge. -/
def routedDeletionRule (V : Type u) :
    CT2.LocalDeletionClosureRule (Target := CT1.Target (ct1Spec V))
      (ct2Capability V) where
  preservesBaseline := (ct2DeletionRule V).preservesBaseline
  targetMonotone := by
    intro object state dart proper admissible baseline reducedTarget
    apply (ct1TargetBridge V).target_of_publicTarget
    apply (ct2DeletionRule V).targetMonotone state dart proper admissible
      baseline
    exact (ct1TargetBridge V).publicTarget_of_target reducedTarget

abbrev localRoute {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  Routes.CT1ToCT2.LocalDeletion.rule (ct2Capability V) (ct1Minimality ctx)

abbrev routedContext {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :=
  Routes.CT1ToCT2.targetContext (ct1Minimality ctx) (ct1AvoidingSource ctx)

/-- An enabled heavy-dart trigger would execute CT2's deletion-C2
contradiction, so exact local discovery is disabled. -/
theorem localRoute_disabled {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    ∃ reject, (localRoute ctx).discover (ct1AvoidingSource ctx) =
      .disabled reject :=
  Routes.CT1ToCT2.LocalDeletion.discover_disabled_of_closure
    (ct1Minimality ctx) (ct1AvoidingSource ctx) (routedDeletionRule V)

private theorem routedDeletionCriticality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 := by
  obtain ⟨reject, disabled⟩ := localRoute_disabled ctx
  have notEligible :=
    Routes.CT1ToCT2.LocalDeletion.disabled_sound disabled dart
  have notHeavy : ¬(4 ≤ ctx.G.degree dart.fst ∧
      4 ≤ ctx.G.degree dart.snd) := by
    rcases notEligible with notProper | notAdmissible
    · exact notProper
    · exact (notAdmissible trivial).elim
  have fstLower : 3 ≤ ctx.G.degree dart.fst :=
    ctx.baseline.trans (ctx.G.minDegree_le_degree dart.fst)
  have sndLower : 3 ≤ ctx.G.degree dart.snd :=
    ctx.baseline.trans (ctx.G.minDegree_le_degree dart.snd)
  omega

/-- In a minimal counterexample, every actual edge has a degree-three
endpoint. -/
theorem deletionCriticality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 :=
  routedDeletionCriticality ctx dart

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
structure VerifiedCT1CT2Prefix {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) : Prop where
  returnSetsDisjoint : ∀ dart : ctx.G.graph.Dart,
    Disjoint (returnSet ctx.G.graph dart) MersenneSet
  ct1Terminal : (minimalCT1Run ctx).result.terminal = .avoiding
  ct1Trace : (minimalCT1Run ctx).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal]
  routeId : (localRoute ctx).routeId =
    "CT1.residual.avoiding->CT2.localDeletion"
  routeDisabled : ∃ reject,
    (localRoute ctx).discover (ct1AvoidingSource ctx) = .disabled reject
  deletionCriticality : ∀ dart : ctx.G.graph.Dart,
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3

def verifiedCT1CT2Prefix {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    VerifiedCT1CT2Prefix ctx where
  returnSetsDisjoint := runAvoidingCT1_returnSets_disjoint
    ctx.G ctx.baseline ctx.avoids
  ct1Terminal := (minimalCT1Run ctx).terminal_eq
  ct1Trace := (minimalCT1Run ctx).trace_eq
  routeId := rfl
  routeDisabled := localRoute_disabled ctx
  deletionCriticality := deletionCriticality ctx

/-- Starting from any supplied counterexample graph on the declared vertex
type, natural-number well-ordering selects an edge-rank-minimal representative
and the framework executes the complete verified CT1-to-CT2 prefix on it.  No
ambient graph universe is enumerated. -/
theorem exists_verifiedCT1CT2Prefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext (problem V) (@Target V),
      (problem V).rank ctx.G ≤ (problem V).rank object ∧
        VerifiedCT1CT2Prefix ctx := by
  let initial : Core.AvoidingContext (problem V) (@Target V) :=
    Core.AvoidingContext.ofBranch (ct1Input object baseline).context avoids
  obtain ⟨ctx, rankLe⟩ :=
    initial.exists_minimalCounterexample (fun _object => ())
  exact ⟨ctx, rankLe, verifiedCT1CT2Prefix ctx⟩

end Erdos64EG.Internal
