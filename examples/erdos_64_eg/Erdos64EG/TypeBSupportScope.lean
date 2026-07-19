import Erdos64EG.CT9FanLabelPacking
import Erdos64EG.CT12InducedP13Packing
import StructuralExhaustion.Graph.RefinedFanLedger

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Assigned Type B support scope

This is the branch-local residual consumed by the degree-four certificate
split and, later, by the B1/B2 resolution.  Its center family is derived from
the literal remainder support.  The optional fan certificate is assigned
data: absence means that the support did not mark that center, not that an
abstract certificate is globally impossible.
-/

structure TypeBSupportScope
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    where
  vertices : Finset ctx.G.Vertex
  assignedCarriers : Finset (Graph.FanClosedPort.LocalCarrier ctx.G.Vertex)
  reserve : Graph.RefinedFanLedger.Reserve ctx.G.Vertex
  assignedMarkedFan : (center : ctx.G.Vertex) →
    Option {fan : MarkedFan ctx // fan.center = center}

namespace TypeBSupportScope

variable
  {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
  (scope : TypeBSupportScope ctx)

noncomputable def coreVertices : Finset ctx.G.Vertex := by
  classical
  exact scope.vertices ∩ p13RemainderVertices ctx

theorem coreVertices_subset_remainder :
    scope.coreVertices ⊆ p13RemainderVertices ctx := by
  classical
  exact Finset.inter_subset_right

theorem coreVertices_subset_vertices :
    scope.coreVertices ⊆ scope.vertices := by
  classical
  exact Finset.inter_subset_left

noncomputable def highCenters : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact scope.coreVertices.filter fun center => 4 ≤ ctx.G.object.degree center

abbrev Center := {center : ctx.G.Vertex // center ∈ scope.highCenters}

@[implicit_reducible]
noncomputable def centers : FinEnum scope.Center := by
  exact Core.Enumeration.finsetSubtype
    ctx.G.object.input.vertices scope.highCenters

@[simp] theorem centers_card :
    scope.centers.card = scope.highCenters.card :=
  Core.Enumeration.finsetSubtype_card
    ctx.G.object.input.vertices scope.highCenters

theorem center_mem_vertices (center : scope.Center) :
    center.1 ∈ scope.vertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact scope.coreVertices_subset_vertices (Finset.mem_filter.mp member).1

theorem center_mem_coreVertices (center : scope.Center) :
    center.1 ∈ scope.coreVertices := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact (Finset.mem_filter.mp member).1

theorem center_high (center : scope.Center) :
    4 ≤ ctx.G.object.degree center.1 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have member := center.2
  change center.1 ∈ scope.coreVertices.filter
    (fun vertex => 4 ≤ ctx.G.object.degree vertex) at member
  exact (Finset.mem_filter.mp member).2

abbrev CertificateAt (center : scope.Center) :=
  {fan : MarkedFan ctx // fan.center = center.1}

def certificateAt (center : scope.Center) : Option (scope.CertificateAt center) :=
  scope.assignedMarkedFan center.1

theorem certificateAt_eq_none_iff (center : scope.Center) :
    scope.certificateAt center = none ↔
      scope.assignedMarkedFan center.1 = none :=
  Iff.rfl

def Assigned (carrier : Graph.FanClosedPort.LocalCarrier ctx.G.Vertex) : Prop :=
  ctx.G.object.graph.Adj carrier.1 carrier.2 ∧
    (carrier ∈ scope.assignedCarriers ∨
      (carrier.1 ∈ scope.coreVertices ∧ carrier.2 ∈ scope.coreVertices))

noncomputable def assignedDecidable : ∀ carrier, Decidable (scope.Assigned carrier) := by
  intro carrier
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  unfold Assigned
  exact inferInstance

end TypeBSupportScope

end Erdos64EG.Internal
