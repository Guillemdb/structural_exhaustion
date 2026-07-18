import Erdos64EG.TypeBEntryRouting
import StructuralExhaustion.Core.FiniteProducedSupportLedger

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

abbrev Ledger := Core.FiniteProducedSupportLedger.Ledger
  (RecordedDecoratedHandoff (ctx := ctx)) ctx.G.Vertex

noncomputable def emptyLedger : Ledger (ctx := ctx) :=
  .empty ctx.G.object.input.vertices.decEq
    RecordedDecoratedHandoff.declaredSupport

/-- Exact invariant inherited from the canonical Type-A component family on
the existing `[108] -> [66]` edge. -/
def PairwiseCoreDisjoint (ledger : Ledger (ctx := ctx)) : Prop :=
  ledger.entries.Pairwise fun left right =>
    Disjoint left.source.core right.source.core

theorem emptyLedger_pairwiseCoreDisjoint :
    PairwiseCoreDisjoint (emptyLedger (ctx := ctx)) := by
  change List.Pairwise _ []
  exact List.Pairwise.nil

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

/-- Acyclic node-[108] connector: execute the existing node-[66] consumer and
append that identical producer output to the F4 ledger. -/
noncomputable def node66AndRecord
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    TypeBEntryRouting.Node66Residual ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe × Ledger (ctx := ctx) :=
  (TypeBEntryRouting.node66 ctx handoff,
    ledger.record (recordedOfExit7 handoff))

theorem node66AndRecord_preserves_consumer
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    (node66AndRecord ledger handoff).1 = TypeBEntryRouting.node66 ctx handoff :=
  rfl

theorem node66AndRecord_appends_exact_handoff
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe) :
    (node66AndRecord ledger handoff).2.entries =
      ledger.entries ++ [recordedOfExit7 handoff] :=
  rfl

/-- Appending one actual node-[108] handoff preserves pairwise core
disjointness exactly when its source core is disjoint from all earlier
produced cores.  This is the theorem-only connector needed to thread the
paper's canonical Type-A family along the unchanged `[108] -> [66]` edge. -/
theorem node66AndRecord_preserves_pairwiseCoreDisjoint
    {ContextSafe ForbiddenFree CoreFree Uncompressible :
      Finset ctx.G.Vertex → Prop}
    {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}
    (ledger : Ledger (ctx := ctx))
    (handoff : TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe)
    (pairwise : PairwiseCoreDisjoint ledger)
    (newDisjoint : ∀ earlier ∈ ledger.entries,
      Disjoint earlier.source.core handoff.source.core) :
    PairwiseCoreDisjoint (node66AndRecord ledger handoff).2 := by
  unfold PairwiseCoreDisjoint at pairwise ⊢
  rw [node66AndRecord_appends_exact_handoff]
  exact List.pairwise_append.mpr ⟨pairwise, by simp, by
    intro earlier earlierMem added addedMem
    simp only [List.mem_singleton] at addedMem
    subst added
    exact newDisjoint earlier earlierMem⟩

end Erdos64EG.Internal.TypeBProducedSupportLedgerConnector
