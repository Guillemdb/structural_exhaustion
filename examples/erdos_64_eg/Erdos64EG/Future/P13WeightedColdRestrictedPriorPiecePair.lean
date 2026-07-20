import Erdos64EG.Future.P13WeightedColdRestrictedPriorStages
import StructuralExhaustion.Graph.FiniteTwoBoundaryPiece

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

/-- Membership in the literal earlier-stage prefix is the expected strict
position inequality; no unordered stage family is inspected. -/
theorem priorStage_val_lt (stage prior : package.Stage)
    (member : prior ∈ package.priorStages stage) :
    prior.val < stage.val := by
  have member := package.priorStages_mem_stages_take stage prior member
  have valuesEq : package.stages.values =
      List.finRange
        (InducedPathRestrictedComponentBoundarySchedule.componentPath
          package.input).support.length :=
    package.profile.stages_values_eq_finRange
  rw [valuesEq] at member
  have indexBound := (List.mem_take_iff_idxOf_lt
    (List.mem_finRange prior)).mp member
  simpa using indexBound

/-- Exact earlier/current induced pieces selected by one coarse-code match.
Each piece keeps its own literal prefix support and maps boundary labels
`0,1` to that prefix's start and endpoint. -/
structure PriorPiecePair (stage prior : package.Stage) where
  prior_mem : prior ∈ package.priorStages stage
  prior_positive : 0 < prior.val
  current_positive : 0 < stage.val
  earlier : FiniteTwoBoundaryPiece.Input
    (InducedPathRestrictedComponentBoundarySchedule.componentObject
      package.input)
  current : FiniteTwoBoundaryPiece.Input
    (InducedPathRestrictedComponentBoundarySchedule.componentObject
      package.input)
  earlier_eq : earlier =
    FiniteTwoBoundaryPiece.ofWalkPrefix package.profile prior prior_positive
  current_eq : current =
    FiniteTwoBoundaryPiece.ofWalkPrefix package.profile stage current_positive

/-- Direct two-boundary pairing for an actual scheduled earlier prefix.  The
positive schedule has already removed stage zero, so this construction has no
extra outcome or residual. -/
noncomputable def priorPiecePair (stage prior : package.Stage)
    (member : prior ∈ package.priorStages stage) :
    package.PriorPiecePair stage prior := by
  have currentPositive : 0 < stage.val :=
    (Nat.zero_le prior.val).trans_lt (package.priorStage_val_lt stage prior member)
  have priorPositive := package.priorStages_mem_positive stage prior member
  exact {
    prior_mem := member
    prior_positive := priorPositive
    current_positive := currentPositive
    earlier := FiniteTwoBoundaryPiece.ofWalkPrefix
      package.profile prior priorPositive
    current := FiniteTwoBoundaryPiece.ofWalkPrefix
      package.profile stage currentPositive
    earlier_eq := rfl
    current_eq := rfl
  }

namespace PriorPiecePair

variable {package : P13WeightedColdRestrictedPrefixPackage ctx node21}
variable {stage prior : package.Stage}
variable (pair : package.PriorPiecePair stage prior)

theorem earlier_support_exact : pair.earlier.support =
    FiniteTwoBoundaryPiece.prefixFinset package.profile prior := by
  rw [pair.earlier_eq]
  rfl

theorem current_support_exact : pair.current.support =
    FiniteTwoBoundaryPiece.prefixFinset package.profile stage := by
  rw [pair.current_eq]
  rfl

theorem earlier_vertex_image :
    Set.range (fun vertex : Fin 2 ⊕ pair.earlier.Internal =>
      (pair.earlier.vertexEquiv vertex).1) =
        (pair.earlier.support : Set
          (InducedPathRestrictedColdSkeleton.component
            package.input.anchor).supp) :=
  pair.earlier.vertex_image_eq_support

theorem current_vertex_image :
    Set.range (fun vertex : Fin 2 ⊕ pair.current.Internal =>
      (pair.current.vertexEquiv vertex).1) =
        (pair.current.support : Set
          (InducedPathRestrictedColdSkeleton.component
            package.input.anchor).supp) :=
  pair.current.vertex_image_eq_support

end PriorPiecePair

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
