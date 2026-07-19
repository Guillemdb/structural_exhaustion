import Erdos64EG.P13ColdGermTerminalRoutes
import StructuralExhaustion.Routes.TargetDefectHandoff

namespace Erdos64EG.P13ColdTargetDefectHandoff

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.PackedBoundariedGluing

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {T : Type u} {boundaries : FinEnum T} [Nonempty T]
variable {ctx : Core.MinimalCounterexampleContext input.problem.{u} input.Target}

abbrev ColdContextDistinction :=
  P13ColdGermLedger.ColdContextDistinction input boundaries ctx

/-- Convert G2's raw distinction to the framework handoff source without
changing either representative or replacing its chosen outside context. -/
def source (distinction : ColdContextDistinction
    (input := input) (boundaries := boundaries) (ctx := ctx)) :
    Routes.TargetDefectHandoff.Source
      (input := input) (boundaries := boundaries) (ctx := ctx) where
  branch := ctx.toBranchContext
  branch_eq := rfl
  left := distinction.replacement
  right := distinction.atom.source
  outside := distinction.outside
  differs := distinction.differs

/-- Exact node-`[156]` typed handoff.  The raw distinction remains bundled
with its consumer residual, preventing a later consumer from substituting a
different germ or outside context. -/
structure RoutedResidual where
  distinction : ColdContextDistinction
    (input := input) (boundaries := boundaries) (ctx := ctx)
  residual : Routes.TargetDefectHandoff.Residual
    (input := input) (boundaries := boundaries) (ctx := ctx)
  exactSource : residual.source = source distinction

/-- Route a concrete G2 distinction without erasing its selected context to
an existential proposition.  This is the provenance-preserving constructor
that a graph-owned G2 producer should call. -/
def routeDistinction
    (distinction : ColdContextDistinction
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    RoutedResidual (input := input) (boundaries := boundaries) (ctx := ctx) :=
  {
    distinction := distinction
    residual := Routes.TargetDefectHandoff.handoff input boundaries ctx
      (source distinction)
    exactSource := rfl
  }

/-- Compatibility adapter for the older proposition-valued terminal.  New
producers should retain their witness and use `routeDistinction` directly. -/
noncomputable def route
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    RoutedResidual (input := input) (boundaries := boundaries) (ctx := ctx) :=
  routeDistinction (Classical.choose previous)

@[simp] theorem routeDistinction_exact
    (distinction : ColdContextDistinction
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (routeDistinction distinction).residual.source = source distinction :=
  (routeDistinction distinction).exactSource

theorem routeDistinction_targetDefective
    (distinction : ColdContextDistinction
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      (routeDistinction distinction).residual.source.left
      (routeDistinction distinction).residual.source.right :=
  (routeDistinction distinction).residual.source.targetDefective

theorem routed_left
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (route previous).residual.source.left =
      (route previous).distinction.replacement := by
  rw [(route previous).exactSource]
  rfl

theorem routed_right
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (route previous).residual.source.right =
      (route previous).distinction.atom.source := by
  rw [(route previous).exactSource]
  rfl

theorem routed_outside
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (route previous).residual.source.outside =
      (route previous).distinction.outside := by
  rw [(route previous).exactSource]
  rfl

theorem routed_targetDefective
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    MinimumDegreeCycleReplacement.TargetDefective input boundaries
      (route previous).residual.source.left
      (route previous).residual.source.right :=
  (route previous).residual.source.targetDefective

theorem routed_ambient
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    (route previous).residual.source.branch.G = ctx.G :=
  Routes.TargetDefectHandoff.ambient_preserved input boundaries ctx
    (route previous).residual.source

theorem routed_provenance
    (previous : P13ColdGermTerminalRoutes.TargetDefectResidual
      (input := input) (boundaries := boundaries) (ctx := ctx)) :
    Routes.TargetDefectHandoff.handoffId =
      "Graph.targetDefect->typedHandoff" :=
  Routes.TargetDefectHandoff.handoff_provenance input boundaries ctx
    (route previous).residual.source

end Erdos64EG.P13ColdTargetDefectHandoff
