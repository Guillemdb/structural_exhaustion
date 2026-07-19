import StructuralExhaustion.Graph.MinimumDegreeCycle
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Graph.MinimumDegreeCycle

open StructuralExhaustion

universe u v

/-!
# Reusable edge-deletion criticality payload

This file packages the two graph consequences of the deletion-only CT2
argument.  It contains no transition or ledger machinery: a manuscript node
can attach this thin graph-owned payload to its existing accumulated stage.
-/

/-- The complete graph-local conclusion of deletion criticality at an
arbitrary minimum-degree threshold. -/
structure DeletionCriticalityFacts
    {V : Type u} {BranchState : FiniteObject V → Type v}
    (input : StaticInput V BranchState)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  tightEndpoint : ∀ dart : ctx.G.graph.Dart,
    ctx.G.degree dart.fst = input.minimumDegree ∨
      ctx.G.degree dart.snd = input.minimumDegree
  slackVerticesIndependent : ∀ {left right : V},
    input.minimumDegree + 1 ≤ ctx.G.degree left →
      input.minimumDegree + 1 ≤ ctx.G.degree right →
        ¬ctx.G.graph.Adj left right

/-- Vertices strictly above the minimum-degree threshold are independent as
an immediate graph-local consequence of the tight-endpoint property.  This
form lets a successor node consume only the endpoint theorem recorded by its
predecessor, without reopening the deletion-criticality construction. -/
theorem slackVerticesIndependent_of_tightEndpoint
    {V : Type u} {BranchState : FiniteObject V → Type v}
    (input : StaticInput V BranchState)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (tightEndpoint : ∀ dart : ctx.G.graph.Dart,
      ctx.G.degree dart.fst = input.minimumDegree ∨
        ctx.G.degree dart.snd = input.minimumDegree) :
    ∀ {left right : V},
      input.minimumDegree + 1 ≤ ctx.G.degree left →
        input.minimumDegree + 1 ≤ ctx.G.degree right →
          ¬ctx.G.graph.Adj left right := by
  intro left right leftHigh rightHigh adjacent
  have critical := tightEndpoint ⟨(left, right), adjacent⟩
  change ctx.G.degree left = input.minimumDegree ∨
    ctx.G.degree right = input.minimumDegree at critical
  rcases critical with leftTight | rightTight <;> omega

/-- Construct the reusable payload from the existing deletion-only CT2
closure theorem.  No edge family is enumerated; both claims are pointwise. -/
def deletionCriticalityFacts
    {V : Type u} {BranchState : FiniteObject V → Type v}
    (input : StaticInput V BranchState)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    DeletionCriticalityFacts input ctx where
  tightEndpoint := input.dart_has_tight_endpoint ctx
  slackVerticesIndependent :=
    slackVerticesIndependent_of_tightEndpoint input ctx
      (input.dart_has_tight_endpoint ctx)

end StructuralExhaustion.Graph.MinimumDegreeCycle

namespace StructuralExhaustion.Graph.PackedMinimumDegreeCycle

open StructuralExhaustion

universe u

/-- Packed counterpart of deletion criticality, stated on the visible graph
inside a lexicographically minimal packed counterexample. -/
structure DeletionCriticalityFacts (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  tightEndpoint : ∀ dart : ctx.G.object.graph.Dart,
    ctx.G.object.degree dart.fst = input.minimumDegree ∨
      ctx.G.object.degree dart.snd = input.minimumDegree
  slackVerticesIndependent : ∀ {left right : ctx.G.Vertex},
    input.minimumDegree + 1 ≤ ctx.G.object.degree left →
      input.minimumDegree + 1 ≤ ctx.G.object.degree right →
        ¬ctx.G.object.graph.Adj left right

/-- Obtain packed deletion criticality through the existing fixed-vertex
projection; no packed graph family is enumerated. -/
def deletionCriticalityFacts (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    DeletionCriticalityFacts input ctx := by
  let facts := MinimumDegreeCycle.deletionCriticalityFacts
    (input.fixed ctx.G.Vertex) (input.fixedContext ctx)
  exact ⟨facts.tightEndpoint, facts.slackVerticesIndependent⟩

end StructuralExhaustion.Graph.PackedMinimumDegreeCycle
