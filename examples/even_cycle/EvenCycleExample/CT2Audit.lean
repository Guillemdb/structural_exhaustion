import EvenCycleExample.CT1Instance

namespace EvenCycleExample.CT2Audit

open StructuralExhaustion

universe u


/-! The graph profile generates the complete deletion-only CT2 API. -/

abbrev pieces (V : Type u) := (staticInput V).ct2Pieces

abbrev capability (V : Type u) := (staticInput V).ct2Capability

abbrev deletionClosureRule (V : Type u) :=
  (staticInput V).ct2DeletionRule

/-- CT2 derives the heavy-edge invariant; it is not an authored obligation. -/
theorem degree_three_endpoint {V : Type u}
    (ctx : Core.MinimalCounterexampleContext
      (problem V) (HasEvenCycle (V := V)))
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = 3 ∨ ctx.G.degree dart.snd = 3 := by
  simpa [staticInput] using (staticInput V).dart_has_tight_endpoint ctx dart

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

end EvenCycleExample.CT2Audit
