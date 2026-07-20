import Erdos64EG.Shared.CT6SparseSurplus
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

/-- Provenance-carrying node `[61]` residual.  The localized support is a
literal connected negative support on the selected minimal graph, and every
counted vertex lies in the exact maximum-`P13`-packing remainder.  The
localization theorem which supplies `support` remains a predecessor obligation;
this structure prevents later Type A/Type B code from silently replacing it by
an unrelated support. -/
structure VerifiedNode61Residual where
  previous : VerifiedSparseSurplusPrefix ctx
  support : NegativeSupport ctx
  core_subset_remainder : support.core ⊆ p13RemainderVertices ctx
  remainder_neighbor_closed : ∀ ⦃vertex neighbor : ctx.G.Vertex⦄,
    vertex ∈ support.core → neighbor ∈ p13RemainderVertices ctx →
      ctx.G.object.graph.Adj vertex neighbor → neighbor ∈ support.core

/-- Exact node `[61]` handoff once negative-charge localization has selected
its connected remainder component. -/
def node61
    (previous : VerifiedSparseSurplusPrefix ctx)
    (support : NegativeSupport ctx)
    (core_subset_remainder : support.core ⊆ p13RemainderVertices ctx)
    (remainder_neighbor_closed : ∀ ⦃vertex neighbor : ctx.G.Vertex⦄,
      vertex ∈ support.core → neighbor ∈ p13RemainderVertices ctx →
        ctx.G.object.graph.Adj vertex neighbor → neighbor ∈ support.core) :
    VerifiedNode61Residual ctx where
  previous := previous
  support := support
  core_subset_remainder := core_subset_remainder
  remainder_neighbor_closed := remainder_neighbor_closed

/-- Exhaustive node `[62]` result on the exact node-`[61]` support. -/
inductive VerifiedNode62Residual (node61 : VerifiedNode61Residual ctx) where
  | high (witness : node61.support.HighSurplusWitness)
  | noHigh
      (highCenters_empty :
        Graph.NegativeSupportHandoff.highCenters ctx.G.object
          node61.support.core = ∅)

/-- Node `[62]` scans only the actual vertices of the localized support.  It
either returns a literal high center or proves that the same finite high-center
set is empty. -/
noncomputable def node62 (node61 : VerifiedNode61Residual ctx) :
    VerifiedNode62Residual ctx node61 := by
  let centers := Graph.NegativeSupportHandoff.highCenters ctx.G.object
    node61.support.core
  by_cases nonempty : centers.Nonempty
  · let center := nonempty.choose
    have centerMember : center ∈ centers := nonempty.choose_spec
    have facts : center ∈ node61.support.core ∧
        4 ≤ ctx.G.object.degree center := by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      simpa [centers, Graph.NegativeSupportHandoff.highCenters] using centerMember
    exact .high {
      center := center
      center_mem := facts.1
      high := facts.2 }
  · exact .noHigh (Finset.not_nonempty_iff_eq_empty.mp nonempty)

theorem node62_high_or_empty (node61 : VerifiedNode61Residual ctx) :
    Nonempty node61.support.HighSurplusWitness ∨
      Graph.NegativeSupportHandoff.highCenters ctx.G.object
        node61.support.core = ∅ := by
  cases node62 ctx node61 with
  | high witness => exact Or.inl ⟨witness⟩
  | noHigh empty => exact Or.inr empty

/-- Node `[62]` performs one local degree test per vertex of the already
localized support. -/
noncomputable def node62Checks (node61 : VerifiedNode61Residual ctx) : Nat :=
  node61.support.core.card

theorem node62Checks_linear (node61 : VerifiedNode61Residual ctx) :
    node62Checks ctx node61 ≤ ctx.G.object.input.vertices.card := by
  unfold node62Checks
  rw [← ctx.G.object.card_vertexFinset]
  apply Finset.card_le_card
  intro vertex _member
  exact ctx.G.object.mem_vertexFinset vertex

/-- Complete node `[64]` residual.  The local support comes from node `[61]`,
the high-center witness is the yes output of node `[62]`, and the earlier
surplus audit is retained on the identical minimal-counterexample context. -/
structure VerifiedNode64Residual where
  node61 : VerifiedNode61Residual ctx
  highSurplus : node61.support.HighSurplusWitness
  routed : Routes.NegativeSupportHandoff.OrdinaryResidual node61.support

namespace VerifiedNode64Residual

/-- The earlier surplus prefix is not rebuilt at node `[64]`; it is projected
from the retained node-`[61]` residual. -/
abbrev previous (residual : VerifiedNode64Residual ctx) :=
  residual.node61.previous

/-- The ordinary Type B support is definitionally the localized node-`[61]`
support. -/
abbrev support (residual : VerifiedNode64Residual ctx) :=
  residual.node61.support

/-- Remainder provenance survives the high-center split unchanged. -/
theorem core_subset_remainder (residual : VerifiedNode64Residual ctx) :
    residual.support.core ⊆ p13RemainderVertices ctx :=
  residual.node61.core_subset_remainder

theorem remainder_neighbor_closed (residual : VerifiedNode64Residual ctx)
    {vertex neighbor : ctx.G.Vertex}
    (vertexMember : vertex ∈ residual.support.core)
    (neighborRemainder : neighbor ∈ p13RemainderVertices ctx)
    (adjacent : ctx.G.object.graph.Adj vertex neighbor) :
    neighbor ∈ residual.support.core :=
  residual.node61.remainder_neighbor_closed vertexMember neighborRemainder adjacent

end VerifiedNode64Residual

/-- Route the exact node `[62]` witness without changing its graph or local
support. -/
def node64
    (node61 : VerifiedNode61Residual ctx)
    (highSurplus : node61.support.HighSurplusWitness) :
    VerifiedNode64Residual ctx where
  node61 := node61
  highSurplus := highSurplus
  routed := Routes.NegativeSupportHandoff.ordinary node61.support highSurplus

@[simp]
theorem node64_support
    (node61 : VerifiedNode61Residual ctx)
    (highSurplus : node61.support.HighSurplusWitness) :
    (node64 ctx node61 highSurplus).support = node61.support :=
  rfl

@[simp]
theorem node64_center
    (node61 : VerifiedNode61Residual ctx)
    (highSurplus : node61.support.HighSurplusWitness) :
    (node64 ctx node61 highSurplus).routed.highSurplus.center =
      highSurplus.center :=
  rfl

/-- The yes-branch center is one of the canonically assigned high centers of
the same negative support; the assigned family is not rebuilt at node `[65]`. -/
theorem node64_center_mem_assignedCenters
    (node61 : VerifiedNode61Residual ctx)
    (highSurplus : node61.support.HighSurplusWitness) :
    (node64 ctx node61 highSurplus).routed.highSurplus.center ∈
      (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
        node61.support.core).assignedCenters := by
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
