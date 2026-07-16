import StructuralExhaustion.Routes.TargetDefectHandoff

namespace StructuralExhaustion.Examples.TargetDefectHandoff

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

/-!
This transfer audit is independent of the Erdős application.  It verifies
that an arbitrary literal graph target defect survives the reusable handoff
with both representatives and its chosen outside context unchanged.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

def transfer
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    Routes.TargetDefectHandoff.Residual
      (input := input) (boundaries := boundaries) (ctx := ctx) :=
  Routes.TargetDefectHandoff.route input boundaries ctx source

theorem transfer_preserves_left
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (transfer source).source.left = source.left :=
  rfl

theorem transfer_preserves_right
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (transfer source).source.right = source.right :=
  rfl

theorem transfer_preserves_outside
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (transfer source).source.outside = source.outside :=
  rfl

theorem transfer_preserves_defect
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      (transfer source).source.left (transfer source).source.right :=
  (transfer source).source.targetDefective

theorem transfer_preserves_ambient
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    source.branch.G = ctx.G :=
  Routes.TargetDefectHandoff.ambient_preserved input boundaries ctx source

theorem transfer_provenance
    (source : Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    Routes.TargetDefectHandoff.routeId =
      "Graph.targetDefect->typedHandoff" :=
  Routes.TargetDefectHandoff.generated_route_id input boundaries ctx source

end StructuralExhaustion.Examples.TargetDefectHandoff
