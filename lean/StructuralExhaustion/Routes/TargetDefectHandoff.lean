import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace StructuralExhaustion.Routes.TargetDefectHandoff

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

/-!
# Exact target-defect handoff

A target defect is a literal outside context distinguishing two boundaried
pieces.  It is not a CT3 compression seed: CT3 consumes the complementary
universal-response branch.  Nor does a target defect by itself contain the
receiver, routed load, quotient support, or charge update required by an
exit-(4) peeling step.

This module therefore provides the smallest sound route contract for the
defect branch.  It transports the two pieces and their actual distinguishing
context without manufacturing any downstream payload.  The selected minimal
counterexample is an index of both the producer and consumer residual, so a
route cannot silently change the ambient object, baseline proof, or branch
state.
-/

variable (input : PackedMinimumDegreeCycle.StaticInput)
variable {T : Type u} (boundaries : FinEnum T) [Nonempty T]
variable (ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target)

/-- Proof-carrying source of a target-defect handoff.  Unlike the existential
`TargetDefective` proposition, this record retains the chosen outside context
as data, which is required by later pressure-token or target-witness consumers. -/
structure Source where
  branch : Core.BranchContext input.problem.{u}
  branch_eq : branch = ctx.toBranchContext
  left : Piece T
  right : Piece T
  outside : Context T
  differs : ¬(input.Target (glue boundaries left outside) ↔
    input.Target (glue boundaries right outside))

namespace Source

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

/-- Forgetting the selected witness recovers exactly the established graph
layer endpoint. -/
def targetDefective (source : Source input boundaries ctx) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      source.left source.right :=
  ⟨source.outside, source.differs⟩

end Source

/-- Consumer-side residual.  No fields beyond the exact source are admitted:
in particular this is not an exit-(4) token or a completed terminal result. -/
structure Residual where
  source : Source input boundaries ctx

/-- Forced identity handoff from the producer endpoint to its typed consumer
residual. -/
def handoff (source : Source input boundaries ctx) :
    Residual input boundaries ctx :=
  ⟨source⟩

@[simp] theorem handoff_source (source : Source input boundaries ctx) :
    (handoff input boundaries ctx source).source = source :=
  rfl

@[simp] theorem handoff_left (source : Source input boundaries ctx) :
    (handoff input boundaries ctx source).source.left = source.left :=
  rfl

@[simp] theorem handoff_right (source : Source input boundaries ctx) :
    (handoff input boundaries ctx source).source.right = source.right :=
  rfl

@[simp] theorem handoff_outside (source : Source input boundaries ctx) :
    (handoff input boundaries ctx source).source.outside = source.outside :=
  rfl

/-- The graph-layer target defect obtained after routing is the same literal
outside-context distinction carried by the producer. -/
theorem handoff_targetDefective (source : Source input boundaries ctx) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      (handoff input boundaries ctx source).source.left
      (handoff input boundaries ctx source).source.right :=
  (handoff input boundaries ctx source).source.targetDefective

/-- Context provenance is definitionally fixed by the dependent route index. -/
theorem branchContext_preserved (source : Source input boundaries ctx) :
    source.branch = ctx.toBranchContext :=
  source.branch_eq

theorem ambient_preserved (source : Source input boundaries ctx) :
    source.branch.G = ctx.G := by
  rw [source.branch_eq]

theorem baseline_preserved (source : Source input boundaries ctx) :
    ctx.toBranchContext.baseline = ctx.baseline :=
  rfl

theorem state_preserved (source : Source input boundaries ctx) :
    ctx.toBranchContext.state = ctx.state :=
  rfl

/-- Stable provenance identifier for consumers and web audits. -/
def handoffId : String :=
  "Graph.targetDefect->typedHandoff"

theorem handoff_provenance (_source : Source input boundaries ctx) :
    handoffId = "Graph.targetDefect->typedHandoff" :=
  rfl

end StructuralExhaustion.Routes.TargetDefectHandoff
