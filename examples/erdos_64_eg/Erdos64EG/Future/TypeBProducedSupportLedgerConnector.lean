import Erdos64EG.Future.TypeBEntryRouting

namespace Erdos64EG.Internal.TypeBProducedSupportLedgerConnector

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

/-!
# Append-only connector for actual decorated Type-B handoffs

The connector records a node-[108] exit-(7) handoff at the same moment that
`TypeBEntryRouting.node66` consumes it.  It stores the literal source core,
decoration center, first-neighbour set, and every proof-carrying arm support.
No family coverage or later Type-B conclusion is assumed.
-/

structure RecordedDecoratedHandoff where
  ContextSafe : Finset ctx.G.Vertex → Prop
  ForbiddenFree : Finset ctx.G.Vertex → Prop
  CoreFree : Finset ctx.G.Vertex → Prop
  Uncompressible : Finset ctx.G.Vertex → Prop
  FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop
  source : Graph.NegativeSupportHandoff.ConnectedNegativeSupport ctx.G.object
  handoff : Graph.NegativeSupportHandoff.DecoratedHandoff ctx.G.object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source

namespace RecordedDecoratedHandoff

noncomputable def armSupport (entry : RecordedDecoratedHandoff (ctx := ctx)) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Finset.univ.biUnion fun first :
      {vertex : ctx.G.Vertex // vertex ∈ entry.handoff.firstNeighbors} =>
    entry.handoff.arm first |>.path.support.toFinset

/-- Exact declared envelope support named by the paper: counted core,
decoration center, first neighbours, and the union of all retained arms. -/
noncomputable def declaredSupport
    (entry : RecordedDecoratedHandoff (ctx := ctx)) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact entry.source.core ∪ {entry.handoff.center} ∪
    entry.handoff.firstNeighbors ∪ entry.armSupport

theorem source_core_subset_declaredSupport
    (entry : RecordedDecoratedHandoff (ctx := ctx)) :
    entry.source.core ⊆ entry.declaredSupport := by
  intro vertex member
  simp [declaredSupport, member]

theorem center_mem_declaredSupport
    (entry : RecordedDecoratedHandoff (ctx := ctx)) :
    entry.handoff.center ∈ entry.declaredSupport := by
  simp [declaredSupport]

theorem center_high
    (entry : RecordedDecoratedHandoff (ctx := ctx)) :
    4 ≤ ctx.G.object.degree entry.handoff.center :=
  entry.handoff.center_high

end RecordedDecoratedHandoff

noncomputable def recordedOfExit7
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    RecordedDecoratedHandoff (ctx := ctx) where
  ContextSafe := ContextSafe
  ForbiddenFree := ForbiddenFree
  CoreFree := CoreFree
  Uncompressible := Uncompressible
  FanSafe := FanSafe
  source := handoff.source
  handoff := handoff.decorated

end Erdos64EG.Internal.TypeBProducedSupportLedgerConnector
