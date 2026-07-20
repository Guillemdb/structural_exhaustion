import Erdos64EG.Future.TypeAReceiverEntryChannels
import Erdos64EG.Future.TypeBEntryRouting
import StructuralExhaustion.Graph.TypeASeparatorHandoff

namespace Erdos64EG.Internal.TypeANodes107To108Handoff

open StructuralExhaustion

universe u v w x y

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

abbrev Node61 := TypeBEntryRouting.VerifiedNode61Residual ctx
abbrev Node63 (node61 : Node61 (ctx := ctx)) :=
  TypeANode63Support.VerifiedNode63Residual (ctx := ctx) node61
abbrev Port (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61) :=
  TypeACompletionPortCoordinates.Coordinate (ctx := ctx) node61 node63

/-- Original node `[95]` on the existing dependency-ready receiver-entry
channel: the assembled anchored return cannot realize exit (1), because its
Mersenne length would be a forbidden target in the same selected graph. -/
theorem node95_exit1_closed (node61 : Node61 (ctx := ctx))
    (node63 : Node63 node61) (port : Port node61 node63)
    (channel : TypeAReceiverEntryChannels.Channel node61 node63 port) :
    ¬MersenneLength
      ((TypeAReceiverEntryChannels.connector node61 node63 port).length
          ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port) +
        channel.length ctx.G.object node63.typeAProfile port
          (TypeAAnchoredReturnCoordinates.anchoredReturn node61 node63 port)
          (TypeAFirstEntryCoordinates.firstEntry node61 node63 port)) :=
  TypeAReceiverEntryChannels.spectral_pressure node61 node63 port channel

abbrev Family (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (port : Port node61 node63)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y) :=
  Graph.TypeADeclaredContinuationCoordinate.Family ctx.G.object
    node63.typeAProfile port Label SupportDatum Value Fibre

abbrev Separator {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {port : Port node61 node63}
    {Label : Type v} {SupportDatum : Type w} {Value : Type x} {Fibre : Type y}
    (family : Family node61 node63 port Label SupportDatum Value Fibre) :=
  Graph.TypeADeclaredContinuationCoordinate.Family.Separator ctx.G.object
    node63.typeAProfile port family

/-- Exact survivor contract at original node `[107]`.  It contains no new
diagram outcome: `separator` is the first-separator output already computed by
the continuation classifier; `center_high` is precisely cubic-switch
absorption after exits (4)--(6) have failed; and `pairwise_fan_safe` is the
five-clause fan-safety conclusion after exits (2)--(6) have failed. -/
structure VerifiedNode107Residual
    (node61 : Node61 (ctx := ctx)) (node63 : Node63 node61)
    (port : Port node61 node63)
    (Label : Type v) (SupportDatum : Type w) (Value : Type x) (Fibre : Type y)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset ctx.G.Vertex → Prop)
    (FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop) where
  family : Family node61 node63 port Label SupportDatum Value Fibre
  separator : Separator family
  cubic_switch_absorbed :
    ctx.G.object.degree
      (separator.vertex ctx.G.object node63.typeAProfile port) = 3 → False
  fan_failure_absorbed :
    ¬FanSafe (separator.vertex ctx.G.object node63.typeAProfile port)
      (separator.leftNext ctx.G.object node63.typeAProfile port)
      (separator.rightNext ctx.G.object node63.typeAProfile port) → False
  fan_safe_symmetric : ∀ ⦃center left right⦄,
    FanSafe center left right → FanSafe center right left
  context_safe : ContextSafe node61.support.core
  forbidden_free : ForbiddenFree node61.support.core
  core_free : CoreFree node61.support.core
  uncompressible : Uncompressible node61.support.core

namespace VerifiedNode107Residual

variable
  {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
  {port : Port node61 node63}
  {Label : Type v} {SupportDatum : Type w} {Value : Type x} {Fibre : Type y}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset ctx.G.Vertex → Prop}
  {FanSafe : ctx.G.Vertex → ctx.G.Vertex → ctx.G.Vertex → Prop}

/-- The numerical part of cubic-switch absorption: ambient minimum degree is
three, and the absorbed cubic alternative excludes equality, so the surviving
separator has degree at least four. -/
theorem center_high
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    4 ≤ ctx.G.object.degree
      (node107.separator.vertex ctx.G.object node63.typeAProfile port) := by
  have lower : 3 ≤ ctx.G.object.degree
      (node107.separator.vertex ctx.G.object node63.typeAProfile port) :=
    ctx.baseline.trans (ctx.G.object.minDegree_le_degree _)
  have notCubic : ctx.G.object.degree
      (node107.separator.vertex ctx.G.object node63.typeAProfile port) ≠ 3 :=
    node107.cubic_switch_absorbed
  omega

theorem pairwise_fan_safe
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    FanSafe (node107.separator.vertex ctx.G.object node63.typeAProfile port)
      (node107.separator.leftNext ctx.G.object node63.typeAProfile port)
      (node107.separator.rightNext ctx.G.object node63.typeAProfile port) := by
  by_contra failure
  exact node107.fan_failure_absorbed failure

noncomputable def firstNeighbors
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact {node107.separator.leftNext ctx.G.object node63.typeAProfile port,
    node107.separator.rightNext ctx.G.object node63.typeAProfile port}

theorem firstNeighbors_nonempty
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    node107.firstNeighbors.Nonempty := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact ⟨node107.separator.leftNext ctx.G.object node63.typeAProfile port, by
    simp [firstNeighbors]⟩

private noncomputable def selectedArm
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe)
    (first : {vertex : ctx.G.Vertex // vertex ∈ node107.firstNeighbors}) :
    Graph.NegativeSupportHandoff.Arm ctx.G.object node61.support.core
      (node107.separator.vertex ctx.G.object node63.typeAProfile port) := by
  let left := node107.separator.leftNext ctx.G.object node63.typeAProfile port
  let right := node107.separator.rightNext ctx.G.object node63.typeAProfile port
  by_cases isLeft : first.1 = left
  · exact (Graph.TypeASeparatorHandoff.Separator.leftArm ctx.G.object
      node63.typeAProfile port node107.separator).castCore node63.profile_support
  · have isRight : first.1 = right := by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      have cases := first.2
      simp only [firstNeighbors, Finset.mem_insert, Finset.mem_singleton] at cases
      exact cases.resolve_left isLeft
    exact (Graph.TypeASeparatorHandoff.Separator.rightArm ctx.G.object
      node63.typeAProfile port node107.separator).castCore node63.profile_support

private theorem selectedArm_first
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe)
    (first : {vertex : ctx.G.Vertex // vertex ∈ node107.firstNeighbors}) :
    (node107.selectedArm first).first = first.1 := by
  let left := node107.separator.leftNext ctx.G.object node63.typeAProfile port
  let right := node107.separator.rightNext ctx.G.object node63.typeAProfile port
  by_cases isLeft : first.1 = left
  · rw [selectedArm]
    split <;> rename_i branch
    · simpa [isLeft, left] using
        Graph.TypeASeparatorHandoff.Separator.leftArm_first ctx.G.object
          node63.typeAProfile port node107.separator
    · exact (branch isLeft).elim
  · have isRight : first.1 = right := by
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      have cases := first.2
      simp only [firstNeighbors, Finset.mem_insert, Finset.mem_singleton] at cases
      exact cases.resolve_left isLeft
    rw [selectedArm]
    split <;> rename_i branch
    · exact (isLeft branch).elim
    · simpa [isRight, right] using
        Graph.TypeASeparatorHandoff.Separator.rightArm_first ctx.G.object
          node63.typeAProfile port node107.separator

/-- Original node `[108]`: construct the literal decorated Type-B handoff from
the surviving node-`[107]` separator.  The counted core is definitionally the
same node-`[61]` negative support, and the two arms are suffixes of the actual
stored connector paths. -/
noncomputable def node108
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    TypeBEntryRouting.Exit7Handoff ctx ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe where
  source := node61.support
  decorated := {
    source_has_no_high_center := node63.highCenters_empty
    center := node107.separator.vertex ctx.G.object node63.typeAProfile port
    center_high := node107.center_high
    firstNeighbors := node107.firstNeighbors
    firstNeighbors_nonempty := node107.firstNeighbors_nonempty
    arm := node107.selectedArm
    arm_first := node107.selectedArm_first
    pairwiseFanSafe := by
      intro left right leftMem rightMem distinct
      letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
      have leftCases : left = node107.separator.leftNext ctx.G.object
          node63.typeAProfile port ∨
          left = node107.separator.rightNext ctx.G.object node63.typeAProfile port := by
        simpa [firstNeighbors] using leftMem
      have rightCases : right = node107.separator.leftNext ctx.G.object
          node63.typeAProfile port ∨
          right = node107.separator.rightNext ctx.G.object node63.typeAProfile port := by
        simpa [firstNeighbors] using rightMem
      rcases leftCases with rfl | rfl <;> rcases rightCases with rfl | rfl
      · exact (distinct rfl).elim
      · exact node107.pairwise_fan_safe
      · exact node107.fan_safe_symmetric node107.pairwise_fan_safe
      · exact (distinct rfl).elim
    contextSafe := node107.context_safe
    forbiddenFree := node107.forbidden_free
    coreFree := node107.core_free
    uncompressible := node107.uncompressible }

@[simp] theorem node108_source
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    (node107.node108).source = node61.support :=
  rfl

@[simp] theorem node108_center
    (node107 : VerifiedNode107Residual node61 node63 port Label SupportDatum
      Value Fibre ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    (node107.node108).decorated.center =
      node107.separator.vertex ctx.G.object node63.typeAProfile port :=
  rfl

end VerifiedNode107Residual

end Erdos64EG.Internal.TypeANodes107To108Handoff
