import StructuralExhaustion.Graph.InducedPathComponentD7Response

namespace StructuralExhaustion.Graph.FiniteActiveInterfaceD7Response

open StructuralExhaustion

universe u

/-!
# D7 responses restricted to one finite active interface

The manuscript retains only declared coordinates whose complete support lies
in the bounded active interface.  This module performs exactly that filter on
the existing sparse-surplus D7 family.  An arbitrary outside context is then
restricted symbolically to its Boolean vector on this finite family; outside
contexts themselves are never enumerated.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

/-- One proof-declared active interface and its constant-size certificate. -/
structure Interface where
  support : Finset ctx.G.Vertex
  bound : Nat
  card_le : support.card ≤ bound

namespace Interface

variable (interface : Interface (ctx := ctx))

def SupportContained (pair : SurplusPairResponse.FreePair stage) : Prop :=
  pair.support stage ⊆ interface.support

noncomputable def supportContainedDecidable
    (pair : SurplusPairResponse.FreePair stage) :
    Decidable (interface.SupportContained stage pair) := by
  classical
  unfold SupportContained
  infer_instance

/-- Exact sparse-surplus coordinates supported by this interface. -/
abbrev Coordinate :=
  {pair : SurplusPairResponse.FreePair stage //
    interface.SupportContained stage pair}

@[implicit_reducible]
noncomputable def coordinates : FinEnum (interface.Coordinate stage) :=
  Core.Enumeration.subtype
    (SurplusPairResponse.freePairEnumeration stage)
    (interface.SupportContained stage)
    (interface.supportContainedDecidable stage)

theorem coordinate_support_subset (coordinate : interface.Coordinate stage) :
    coordinate.1.support stage ⊆ interface.support :=
  coordinate.2

theorem coordinate_support_card_le (coordinate : interface.Coordinate stage) :
    (coordinate.1.support stage).card ≤ interface.bound :=
  (Finset.card_le_card coordinate.2).trans interface.card_le

/-- Context-indexed D7 response on precisely the filtered family. -/
noncomputable def responseProfile :
    FiniteSupportResponse.Profile input ctx (interface.Coordinate stage) where
  coordinates := interface.coordinates stage
  support := fun coordinate => coordinate.1.support stage

theorem response_true_iff (coordinate : interface.Coordinate stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    (interface.responseProfile stage).responseSystem.response
        coordinate outside = true ↔
      input.Target
        (PackedBoundariedGluing.glue ctx.G.object.input.vertices
          ((interface.responseProfile stage).coordinatePiece coordinate)
          outside) :=
  (interface.responseProfile stage).response_true_iff coordinate outside

/-- The finite-shape D7 code: one Boolean for each declared local coordinate.
It is used only as the codomain of symbolic restriction; production CT7 does
not enumerate this Boolean cube. -/
abbrev ContextCode := interface.Coordinate stage → Bool

/-- Restriction of a literal outside context to the complete local D7 vector.
This is a projection, not an outside-context enumeration. -/
noncomputable def restrictContext
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    interface.ContextCode stage :=
  fun coordinate =>
    (interface.responseProfile stage).responseSystem.response
      coordinate outside

theorem restrictContext_apply
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex)
    (coordinate : interface.Coordinate stage) :
    interface.restrictContext stage outside coordinate =
      (interface.responseProfile stage).responseSystem.response
        coordinate outside := rfl

/-- Symbolic encoding: every outside context has its exact finite D7
restriction.  This is deliberately one-way and is not a decode/reflection
theorem for a CT7 context table. -/
theorem contextEncoding
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    ∃ code : interface.ContextCode stage,
      code = interface.restrictContext stage outside :=
  ⟨interface.restrictContext stage outside, rfl⟩

theorem coordinates_card_le_freePairs :
    (interface.coordinates stage).card ≤
      (SurplusPairResponse.freePairEnumeration stage).card :=
  Core.Enumeration.subtype_card_le
    (SurplusPairResponse.freePairEnumeration stage)
    (interface.SupportContained stage)
    (interface.supportContainedDecidable stage)

end Interface

end StructuralExhaustion.Graph.FiniteActiveInterfaceD7Response
