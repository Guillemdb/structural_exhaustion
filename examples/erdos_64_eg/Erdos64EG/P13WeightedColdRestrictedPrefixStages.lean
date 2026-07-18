import Erdos64EG.P13WeightedColdRestrictedComponentSchedule
import StructuralExhaustion.Graph.WalkPrefixFiltration

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable def p13RestrictedPrefixProfile
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21)) :
    WalkPrefixFiltration.Profile
      (InducedPathRestrictedComponentBoundarySchedule.componentPath input) :=
  ⟨InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath input⟩

/-- C153.2 package constructed only from a C153.1b component constructor.
The path is not a field: the sole profile is definitionally built from the
stored restricted component input. -/
structure P13WeightedColdRestrictedPrefixPackage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 3) where
  entry : P13WeightedColdRestrictedEntry ctx node21
  boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
    (P13ColdFamily (ctx := ctx) (node21 := node21))
  tokenExact : boundary.token = entry.source.2.stub.token
  routeExact : entry.route = .componentBoundary boundary tokenExact
  input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21)
  inputExact : input =
    p13RestrictedComponentInputOfBoundary entry boundary tokenExact

/-- Thin constructor for the exact C153.1b component payload. -/
def p13RestrictedPrefixPackageOfComponent
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (routeExact : entry.route = .componentBoundary boundary tokenExact)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact) :
    P13WeightedColdRestrictedPrefixPackage ctx node21 :=
  ⟨entry, boundary, tokenExact, routeExact, input, inputExact⟩

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

noncomputable def profile := p13RestrictedPrefixProfile package.input

abbrev Stage := package.profile.Stage

noncomputable def stages : Core.OrderedCollection package.Stage :=
  package.profile.stages

noncomputable def prefixSupport (stage : package.Stage) :
    List (InducedPathRestrictedColdSkeleton.component
      package.input.anchor).supp :=
  package.profile.prefixSupport stage

theorem source_token_exact :
    package.input.anchor.token = package.entry.source.2.stub.token := by
  rw [package.inputExact]
  exact package.tokenExact

theorem stages_nodup : package.stages.values.Nodup :=
  package.profile.stages_nodup

theorem stages_length :
    package.stages.values.length =
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).support.length :=
  package.profile.stages_length

theorem prefixSupport_nodup (stage : package.Stage) :
    (package.prefixSupport stage).Nodup :=
  package.profile.prefixSupport_nodup stage

theorem prefixSupport_nonempty (stage : package.Stage) :
    package.prefixSupport stage ≠ [] :=
  package.profile.prefixSupport_nonempty stage

theorem prefixSupport_subset_path (stage : package.Stage) :
    package.prefixSupport stage ⊆
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).support :=
  package.profile.prefixSupport_subset_path stage

theorem prefixSupport_prefix {earlier later : package.Stage}
    (ordered : earlier.val ≤ later.val) :
    package.prefixSupport earlier <+: package.prefixSupport later :=
  package.profile.prefixSupport_prefix ordered

theorem prefixSupport_subset {earlier later : package.Stage}
    (ordered : earlier.val ≤ later.val) :
    package.prefixSupport earlier ⊆ package.prefixSupport later :=
  package.profile.prefixSupport_subset ordered

/-- Visible work is one prefix descriptor per stored component-path vertex. -/
noncomputable def checks : Nat := package.profile.checks

theorem checks_eq_path_support :
    package.checks =
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).support.length := rfl

theorem checks_le_componentCarrier :
    package.checks ≤
      (InducedPathRestrictedComponentBoundarySchedule.componentObject
        package.input).input.vertices.card := by
  rw [package.checks_eq_path_support]
  exact InducedPathRestrictedComponentBoundarySchedule.componentPath_support_length_le_component
    package.input

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
