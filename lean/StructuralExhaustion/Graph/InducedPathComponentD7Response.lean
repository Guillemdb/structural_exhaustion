import StructuralExhaustion.Graph.InducedPathComponentD7

namespace StructuralExhaustion.Graph.InducedPathComponentD7Response

open StructuralExhaustion

universe u

/-!
# Context-indexed D7 responses on one component support

This module restricts the existing sparse-pair response profile to exactly the
D7 coordinates whose declared support lies in one retained component
interface.  Responses remain universally parameterized by a supplied outside
context.  In particular, this is not a context-free Boolean semantics and does
not discharge clause D7 in the fixed two-boundary cut state.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput :
  InducedPathComponentBoundarySchedule.Input ctx.G.object)

/-- The exact component-local restriction of the graph-owned sparse-pair
response profile. -/
noncomputable def responseProfile :
    FiniteSupportResponse.Profile input ctx
      (InducedPathComponentD7.Coordinate stage componentInput) where
  coordinates := InducedPathComponentD7.coordinates stage componentInput
  support := fun coordinate ↦ coordinate.1.support stage

/-- The restricted profile uses exactly the already constructed D7 schedule. -/
theorem coordinates_exact :
    (responseProfile stage componentInput).coordinates =
      InducedPathComponentD7.coordinates stage componentInput :=
  rfl

/-- The support inherited from the global pair profile is exactly the support
named by the component D7 coordinate. -/
theorem support_exact
    (coordinate : InducedPathComponentD7.Coordinate stage componentInput) :
    (responseProfile stage componentInput).support coordinate =
      coordinate.support stage componentInput :=
  rfl

/-- The literal supported piece is unchanged by restricting the coordinate
schedule. -/
theorem coordinatePiece_eq_sparsePairPiece
    (coordinate : InducedPathComponentD7.Coordinate stage componentInput) :
    (responseProfile stage componentInput).coordinatePiece coordinate =
      (SurplusPairResponse.responseProfile stage).coordinatePiece coordinate.1 := by
  apply congrArg (FiniteSupportResponse.piece ctx.G.object)
  rfl

/-- The restricted response is the actual target predicate after gluing the
coordinate's declared support to the supplied outside context. -/
theorem response_true_iff
    (coordinate : InducedPathComponentD7.Coordinate stage componentInput)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    (responseProfile stage componentInput).responseSystem.response
        coordinate outside = true ↔
      input.Target
        (PackedBoundariedGluing.glue ctx.G.object.input.vertices
          ((responseProfile stage componentInput).coordinatePiece coordinate)
          outside) :=
  (responseProfile stage componentInput).response_true_iff coordinate outside

/-- Pointwise provenance: restricting the coordinate schedule changes neither
its support nor its context-indexed sparse-pair response. -/
theorem response_eq_sparsePairResponse
    (coordinate : InducedPathComponentD7.Coordinate stage componentInput)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    (responseProfile stage componentInput).responseSystem.response
        coordinate outside =
      (SurplusPairResponse.responseProfile stage).responseSystem.response
        coordinate.1 outside := by
  change
    @decide
        (input.Target
          (PackedBoundariedGluing.glue ctx.G.object.input.vertices
            ((responseProfile stage componentInput).coordinatePiece coordinate)
            outside))
        (Classical.propDecidable _) =
      @decide
        (input.Target
          (PackedBoundariedGluing.glue ctx.G.object.input.vertices
            ((SurplusPairResponse.responseProfile stage).coordinatePiece
              coordinate.1) outside))
        (Classical.propDecidable _)
  rw [coordinatePiece_eq_sparsePairPiece stage componentInput coordinate]

end StructuralExhaustion.Graph.InducedPathComponentD7Response
