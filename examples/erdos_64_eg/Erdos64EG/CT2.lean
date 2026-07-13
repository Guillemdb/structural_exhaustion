import Erdos64EG.CT1

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

/-- In a minimal counterexample, every actual edge has a degree-three
endpoint. -/
theorem deletionCriticality {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 :=
  (staticInput V).dart_has_tight_endpoint ctx dart

/-- Exact deletion-C2 execution for an explicitly supplied heavy dart. -/
def heavyDartRun {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V))
    (dart : ctx.G.graph.Dart)
    (heavy : 4 ≤ ctx.G.degree dart.fst ∧
      4 ≤ ctx.G.degree dart.snd) :
    CT2.LocalDeletionRun (ct2Capability V) ctx
      ⟨⟨dart, heavy, trivial⟩⟩ :=
  (staticInput V).heavyDartRun ctx dart heavy

end Erdos64EG.Internal
