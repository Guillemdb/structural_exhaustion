import Mathlib.Tactic
import StructuralExhaustion.CT7.Automation
import StructuralExhaustion.Graph.MinimumDegreeCycle

namespace StructuralExhaustion.Graph.AdjacencyResponse

open StructuralExhaustion

universe u

/-!
# Exact finite adjacency-response comparison

This graph profile compares two vertices on the complete declared vertex
context.  Realization is deliberately absent; CT7 therefore returns either
the first vertex on which their adjacency responses differ or a certificate
that the two response vectors agree everywhere.  Only two linear passes over
the declared vertex order are available to the runner.
-/

def spec (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)) :
    CT7.Spec base.problem where
  Object := V
  Context := V
  Realizes := fun _ctx _vertex _context => False
  response := fun ctx vertex context =>
    @decide (ctx.G.graph.Adj vertex context)
      (ctx.G.input.decideAdj vertex context)

def capability (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)) :
    CT7.Capability (spec base) where
  contexts := fun ctx _left _right => ctx.G.input.vertices
  realizesDecidable := fun _ctx _vertex _context => isFalse id

def context (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    Core.BranchContext base.problem :=
  ⟨object, baseline, ()⟩

def input (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (left right : V) : CT7.Input (spec base) (context base object baseline) :=
  ⟨left, right⟩

def run (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (left right : V) :=
  CT7.run (spec base) (capability base) (context base object baseline)
    (input base object baseline left right)

theorem stateSpace
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (left right : V) :
    (∃ vertex : V,
        (spec base).response (context base object baseline) left vertex ≠
          (spec base).response (context base object baseline) right vertex) ∨
      (∀ vertex : V,
        (spec base).response (context base object baseline) left vertex =
          (spec base).response (context base object baseline) right vertex) := by
  generalize resultEquation : run base object baseline left right = result
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | realization certificate => exact certificate.realizes.elim
      | distinguishing residual =>
          exact Or.inl ⟨residual.context, residual.differs⟩
      | neutral certificate => exact Or.inr certificate.allEqual

theorem response_true_iff
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (vertex contextVertex : V) :
    (spec base).response (context base object baseline) vertex contextVertex = true ↔
      object.graph.Adj vertex contextVertex := by
  simp [spec, context]

def checks (object : FiniteObject V) : Nat :=
  2 * object.input.vertices.card

theorem checks_linear (object : FiniteObject V) :
    checks object ≤ 2 * object.input.vertices.card + 1 := by
  unfold checks
  omega

structure VerifiedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (left right : V) : Prop where
  verified : (run base object baseline left right).outcome.Valid
  traceValid : CT7.Graph.ValidTrace (spec base) (capability base)
    (context base object baseline) (input base object baseline left right)
    (run base object baseline left right).trace
  total : ∃ result,
    result = run base object baseline left right ∧ result.outcome.Valid
  stateSpace :
    (∃ vertex : V,
        (spec base).response (context base object baseline) left vertex ≠
          (spec base).response (context base object baseline) right vertex) ∨
      (∀ vertex : V,
        (spec base).response (context base object baseline) left vertex =
          (spec base).response (context base object baseline) right vertex)
  polynomial : checks object ≤ 2 * object.input.vertices.card + 1

def verifiedStage
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (left right : V) : VerifiedStage base object baseline left right where
  verified := CT7.run_verified _ _ _ _
  traceValid := CT7.run_trace_valid _ _ _ _
  total := ⟨_, rfl, CT7.run_verified _ _ _ _⟩
  stateSpace := stateSpace base object baseline left right
  polynomial := checks_linear object

end StructuralExhaustion.Graph.AdjacencyResponse
