import Erdos64EG.P13WeightedColdRestrictedPrefixStages

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-!
# Exact global schedule of node-[153] component-prefix packages

This list-level connector filters only actual `.component` constructors from
the computed node-[152] schedule and retains their complete dependent payload.
Cross-window constructors remain on their original edge; no ambient family is
enumerated.
-/

abbrev P13WeightedColdRestrictedScheduledOccurrence
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :=
  Sigma fun entry : P13WeightedColdRestrictedEntry ctx node21 =>
    P13WeightedColdRestrictedScheduledResult entry

noncomputable def p13WeightedColdRestrictedPrefixPackage?
    (scheduled : P13WeightedColdRestrictedScheduledOccurrence ctx node21) :
    Option (P13WeightedColdRestrictedPrefixPackage ctx node21) :=
  match scheduled.2 with
  | .component boundary tokenExact routeExact input inputExact =>
      some (p13RestrictedPrefixPackageOfComponent scheduled.1 boundary
        tokenExact routeExact input inputExact)
  | .crossWindow _ _ => none

/-- Every actual component result, in the inherited node-[152] order. -/
noncomputable def p13WeightedColdRestrictedPrefixPackages :
    List (P13WeightedColdRestrictedPrefixPackage ctx node21) :=
  (p13WeightedColdRestrictedComponentSchedule
    (ctx := ctx) (node21 := node21)).filterMap
      p13WeightedColdRestrictedPrefixPackage?

/-- A literal component occurrence is retained with the identical entry,
boundary, route equality, and component input. -/
theorem componentOccurrence_mem_prefixPackages
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (routeExact : entry.route = .componentBoundary boundary tokenExact)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact)
    (member : (Sigma.mk entry
      (.component boundary tokenExact routeExact input inputExact) :
        P13WeightedColdRestrictedScheduledOccurrence ctx node21) ∈
      p13WeightedColdRestrictedComponentSchedule
        (ctx := ctx) (node21 := node21)) :
    p13RestrictedPrefixPackageOfComponent entry boundary tokenExact routeExact
        input inputExact ∈
      p13WeightedColdRestrictedPrefixPackages
        (ctx := ctx) (node21 := node21) := by
  rw [p13WeightedColdRestrictedPrefixPackages, List.mem_filterMap]
  refine ⟨Sigma.mk entry
    (.component boundary tokenExact routeExact input inputExact), member, ?_⟩
  rfl

/-- Filtering costs at most one constructor match per stored occurrence. -/
theorem p13WeightedColdRestrictedPrefixPackages_length_le :
    (p13WeightedColdRestrictedPrefixPackages
      (ctx := ctx) (node21 := node21)).length ≤
      (p13WeightedColdRestrictedEntries
        (ctx := ctx) (node21 := node21)).length := by
  calc
    (p13WeightedColdRestrictedPrefixPackages
        (ctx := ctx) (node21 := node21)).length ≤
        (p13WeightedColdRestrictedComponentSchedule
          (ctx := ctx) (node21 := node21)).length := by
      exact List.length_filterMap_le _ _
    _ = (p13WeightedColdRestrictedEntries
          (ctx := ctx) (node21 := node21)).length :=
      p13WeightedColdRestrictedComponentSchedule_length

theorem p13WeightedColdRestrictedPrefixPackages_length_le_vertices :
    (p13WeightedColdRestrictedPrefixPackages
      (ctx := ctx) (node21 := node21)).length ≤
      ctx.G.object.input.vertices.card := by
  exact p13WeightedColdRestrictedPrefixPackages_length_le.trans
    p13WeightedColdRestrictedEntryChecks_linear

end Erdos64EG.Internal
