import Erdos64EG.CT6SparseSurplus
import StructuralExhaustion.Routes.NegativeSupportHandoff

namespace Erdos64EG.Internal.TypeBEntryRouting

open StructuralExhaustion

universe u

variable
  (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})

/-- Exact node `[61]` local support type on the selected minimal graph.  Its
net charge is the quarter-unit form of `N(X) < 0`, and its connectivity paths
remain inside the same finite support. -/
abbrev NegativeSupport :=
  Graph.NegativeSupportHandoff.ConnectedNegativeSupport ctx.G.object

/-- Complete node `[64]` residual.  The local support comes from node `[61]`,
the high-center witness is the yes output of node `[62]`, and the earlier
surplus audit is retained on the identical minimal-counterexample context. -/
structure VerifiedNode64Residual where
  previous : VerifiedSparseSurplusPrefix ctx
  support : NegativeSupport ctx
  highSurplus : support.HighSurplusWitness
  routed : Routes.NegativeSupportHandoff.OrdinaryResidual support

/-- Route the exact node `[62]` witness without changing its graph or local
support. -/
def node64
    (previous : VerifiedSparseSurplusPrefix ctx)
    (support : NegativeSupport ctx)
    (highSurplus : support.HighSurplusWitness) :
    VerifiedNode64Residual ctx where
  previous := previous
  support := support
  highSurplus := highSurplus
  routed := Routes.NegativeSupportHandoff.ordinary support highSurplus

@[simp]
theorem node64_support
    (previous : VerifiedSparseSurplusPrefix ctx)
    (support : NegativeSupport ctx)
    (highSurplus : support.HighSurplusWitness) :
    (node64 ctx previous support highSurplus).support = support :=
  rfl

@[simp]
theorem node64_center
    (previous : VerifiedSparseSurplusPrefix ctx)
    (support : NegativeSupport ctx)
    (highSurplus : support.HighSurplusWitness) :
    (node64 ctx previous support highSurplus).routed.highSurplus.center =
      highSurplus.center :=
  rfl

/-- The yes-branch center is one of the canonically assigned high centers of
the same negative support; the assigned family is not rebuilt at node `[65]`. -/
theorem node64_center_mem_assignedCenters
    (previous : VerifiedSparseSurplusPrefix ctx)
    (support : NegativeSupport ctx)
    (highSurplus : support.HighSurplusWitness) :
    (node64 ctx previous support highSurplus).routed.highSurplus.center ∈
      (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
        support.core).assignedCenters := by
  exact highSurplus.center_mem_highCenters

/-- Exact producer type of the dashed node `[108] -> [66]` handoff.  The four
core predicates and the fan-safe relation are the semantic data proved by the
Type A exit-(7) producer; the route below does not infer or strengthen them. -/
abbrev Exit7Handoff
    (ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop)
    (FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop) :=
  Routes.NegativeSupportHandoff.ExitHandoff ctx.G.object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe

/-- Exact consumer type at dashed node `[66]`. -/
abbrev Node66Residual
    (ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop)
    (FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop) :=
  Routes.NegativeSupportHandoff.DecoratedResidual ctx.G.object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe

/-- Node `[66]` consumes precisely the output of node `[108]`; source graph,
counted support, connector arms, and every semantic proof are definitionally
preserved. -/
def node66
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (handoff : Exit7Handoff ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    Node66Residual ctx ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe :=
  Routes.NegativeSupportHandoff.decorated handoff

@[simp]
theorem node66_source
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (handoff : Exit7Handoff ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (node66 ctx handoff).source = handoff.source :=
  rfl

@[simp]
theorem node66_data
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (handoff : Exit7Handoff ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (node66 ctx handoff).decorated = handoff.decorated :=
  rfl

/-- Complete node `[65]` join.  The constructors remain distinct so ordinary
high-surplus predicates cannot be used on the decorated Type A handoff branch,
or conversely.  Both constructors retain their exact context-indexed source. -/
inductive VerifiedNode65Residual
    (ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop)
    (FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop) where
  | ordinary (residual : VerifiedNode64Residual ctx)
  | decorated (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)

namespace VerifiedNode65Residual

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  {ContextSafe ForbiddenFree CoreFree Uncompressible :
    Finset ctx.G.Vertex → Prop}
  {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}

/-- Framework entry view of the branch-tagged node `[65]` residual. -/
def entry :
    VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe →
    Routes.NegativeSupportHandoff.Entry ctx.G.object ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe
  | .ordinary residual => .ordinary residual.support residual.routed
  | .decorated residual => .decorated residual

/-- The exact local source retained through either incoming branch. -/
def source
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) : NegativeSupport ctx :=
  residual.entry.source

theorem negative
    (residual : VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      residual.source.core).netQuarterCharge < 0 :=
  residual.entry.negative

@[simp]
theorem source_ordinary (residual : VerifiedNode64Residual ctx) :
    (VerifiedNode65Residual.ordinary residual :
      VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
        Uncompressible FanSafe).source = residual.support :=
  rfl

@[simp]
theorem source_decorated
    (residual : Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (VerifiedNode65Residual.decorated residual :
      VerifiedNode65Residual ctx ContextSafe ForbiddenFree CoreFree
        Uncompressible FanSafe).source = residual.source :=
  rfl

end VerifiedNode65Residual

end Erdos64EG.Internal.TypeBEntryRouting
