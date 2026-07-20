import Erdos64EG.Future.P13WeightedColdRestrictedPrefixStages
import StructuralExhaustion.Core.FiniteSearch

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

noncomputable def boundedInterfaceWindowSupport
    (_package : P13WeightedColdRestrictedPrefixPackage ctx node21)
    (window : WindowIndex ctx.G.object) : Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Finset.univ.image fun offset : Fin 13 =>
    selectedWindow ctx.G.object window offset

noncomputable def boundedInterfaceCurrentEndpoint
    (stage : package.Stage) : ctx.G.Vertex :=
  ((InducedPathRestrictedComponentBoundarySchedule.componentPath
    package.input).getVert stage.val).1.1

/-- The literal bounded active interface in the paper: two displayed P13
windows and the two active outside boundary endpoints. -/
noncomputable def boundedActiveInterface (stage : package.Stage) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact package.boundedInterfaceWindowSupport package.input.anchor.window ∪
    package.boundedInterfaceWindowSupport
      (InducedPathRestrictedComponentBoundarySchedule.successor
        package.input).window ∪
    {package.input.anchor.neighbor,
      package.boundedInterfaceCurrentEndpoint stage}

set_option maxHeartbeats 800000 in
theorem boundedInterfaceWindowSupport_card_le
    (window : WindowIndex ctx.G.object) :
    (package.boundedInterfaceWindowSupport window).card ≤ 13 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold boundedInterfaceWindowSupport
  calc
    (Finset.univ.image fun offset : Fin 13 =>
      selectedWindow ctx.G.object window offset).card ≤ Finset.univ.card :=
        Finset.card_image_le
    _ = 13 := by simp

theorem boundedActiveInterface_card_le_28 (stage : package.Stage) :
    (package.boundedActiveInterface stage).card ≤ 28 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  let anchor := package.boundedInterfaceWindowSupport package.input.anchor.window
  let successor := package.boundedInterfaceWindowSupport
    (InducedPathRestrictedComponentBoundarySchedule.successor package.input).window
  let endpoints : Finset ctx.G.Vertex :=
    {package.input.anchor.neighbor, package.boundedInterfaceCurrentEndpoint stage}
  have hAnchor : anchor.card ≤ 13 :=
    package.boundedInterfaceWindowSupport_card_le package.input.anchor.window
  have hSuccessor : successor.card ≤ 13 :=
    package.boundedInterfaceWindowSupport_card_le
      (InducedPathRestrictedComponentBoundarySchedule.successor package.input).window
  have hEndpoints : endpoints.card ≤ 2 := by
    change (insert package.input.anchor.neighbor
      ({package.boundedInterfaceCurrentEndpoint stage} :
        Finset ctx.G.Vertex)).card ≤ 2
    calc
      (insert package.input.anchor.neighbor
          ({package.boundedInterfaceCurrentEndpoint stage} :
            Finset ctx.G.Vertex)).card
          ≤ ({package.boundedInterfaceCurrentEndpoint stage} :
            Finset ctx.G.Vertex).card + 1 :=
            Finset.card_insert_le _ _
      _ = 2 := by simp
  rw [boundedActiveInterface]
  change (anchor ∪ successor ∪ endpoints).card ≤ 28
  have first := Finset.card_union_le anchor successor
  have second := Finset.card_union_le (anchor ∪ successor) endpoints
  omega

theorem boundedActiveInterface_card_le_30 (stage : package.Stage) :
    (package.boundedActiveInterface stage).card ≤ 30 :=
  (package.boundedActiveInterface_card_le_28 stage).trans (by omega)

/-- Fixed semantic roles of the 28 carrier occurrences.  The last Boolean is
`false` for the anchor outside endpoint and `true` for the moving endpoint. -/
abbrev BoundedCarrierRole := Fin 13 ⊕ (Fin 13 ⊕ Bool)

@[implicit_reducible]
noncomputable def boundedCarrierRoles
    (_package : P13WeightedColdRestrictedPrefixPackage ctx node21) :
    FinEnum BoundedCarrierRole := by
  letI : FinEnum (Fin 13) := inferInstance
  letI : FinEnum Bool := Core.Enumeration.bool
  infer_instance

theorem boundedCarrierRoles_card :
    package.boundedCarrierRoles.card = 28 := by
  rfl

noncomputable def boundedCarrierRoleVertex (stage : package.Stage) :
    BoundedCarrierRole → ctx.G.Vertex
  | .inl offset => selectedWindow ctx.G.object package.input.anchor.window offset
  | .inr (.inl offset) => selectedWindow ctx.G.object
      (InducedPathRestrictedComponentBoundarySchedule.successor package.input).window offset
  | .inr (.inr false) => package.input.anchor.neighbor
  | .inr (.inr true) => package.boundedInterfaceCurrentEndpoint stage

theorem mem_boundedActiveInterface_iff_role (stage : package.Stage)
    (vertex : ctx.G.Vertex) :
    vertex ∈ package.boundedActiveInterface stage ↔
      ∃ role : BoundedCarrierRole,
        package.boundedCarrierRoleVertex stage role = vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  simp only [boundedActiveInterface, boundedInterfaceWindowSupport,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ((⟨offset, rfl⟩ | ⟨offset, rfl⟩) | endpoint)
    · exact ⟨.inl offset, rfl⟩
    · exact ⟨.inr (.inl offset), rfl⟩
    · rcases endpoint with rfl | rfl
      · exact ⟨.inr (.inr false), rfl⟩
      · exact ⟨.inr (.inr true), rfl⟩
  · rintro ⟨role, rfl⟩
    rcases role with offset | (offset | endpoint)
    · exact Or.inl (Or.inl ⟨offset, rfl⟩)
    · exact Or.inl (Or.inr ⟨offset, rfl⟩)
    · cases endpoint
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- Exact local vertex schedule obtained from the 28 semantic roles.  Role
collisions are deduplicated after mapping, so this never filters the ambient
graph vertex enumeration. -/
@[implicit_reducible] noncomputable def boundedCarrierVertices
    (stage : package.Stage) :
    FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ package.boundedActiveInterface stage} := by
  let roles := package.boundedCarrierRoles
  let values : List {vertex : ctx.G.Vertex //
      vertex ∈ package.boundedActiveInterface stage} :=
    roles.orderedValues.map fun role =>
      ⟨package.boundedCarrierRoleVertex stage role,
        (package.mem_boundedActiveInterface_iff_role stage _).2 ⟨role, rfl⟩⟩
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact FinEnum.ofNodupList values.dedup
    (by
      intro vertex
      apply List.mem_dedup.mpr
      obtain ⟨role, roleExact⟩ :=
        (package.mem_boundedActiveInterface_iff_role stage vertex.1).mp vertex.2
      apply List.mem_map.mpr
      refine ⟨role, roles.mem_orderedValues role, ?_⟩
      apply Subtype.ext
      exact roleExact)
    (List.nodup_dedup values)

theorem boundedCarrierVertices_card_le_28 (stage : package.Stage) :
    (package.boundedCarrierVertices stage).card ≤ 28 := by
  letI : FinEnum {vertex : ctx.G.Vertex //
      vertex ∈ package.boundedActiveInterface stage} :=
    package.boundedCarrierVertices stage
  rw [FinEnum.card_eq_fintypeCard]
  simpa using package.boundedActiveInterface_card_le_28 stage

/-- First fixed semantic role naming one carrier vertex. -/
structure BoundedCarrierCode (stage : package.Stage)
    (vertex : ctx.G.Vertex) where
  role : BoundedCarrierRole
  exact : package.boundedCarrierRoleVertex stage role = vertex

noncomputable def boundedCarrierCode (stage : package.Stage)
    (vertex : ctx.G.Vertex) (member : vertex ∈ package.boundedActiveInterface stage) :
    package.BoundedCarrierCode stage vertex := by
  let result := Core.FiniteSearch.first package.boundedCarrierRoles
    (fun role => package.boundedCarrierRoleVertex stage role = vertex)
    (fun _ => ctx.G.object.input.vertices.decEq _ _)
  cases equation : result with
  | found hit =>
      exact ⟨hit.value, hit.holds⟩
  | absent absent =>
      have existsWitness :=
        (package.mem_boundedActiveInterface_iff_role stage vertex).mp member
      have impossible : False := existsWitness.elim fun role holds =>
        absent role (package.boundedCarrierRoles.mem_orderedValues role) holds
      exact impossible.elim

theorem boundedCarrierCode_injective (stage : package.Stage)
    {left right : ctx.G.Vertex}
    (leftMem : left ∈ package.boundedActiveInterface stage)
    (rightMem : right ∈ package.boundedActiveInterface stage)
    (equal : (package.boundedCarrierCode stage left leftMem).role =
      (package.boundedCarrierCode stage right rightMem).role) : left = right := by
  rw [← (package.boundedCarrierCode stage left leftMem).exact,
    ← (package.boundedCarrierCode stage right rightMem).exact, equal]

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
