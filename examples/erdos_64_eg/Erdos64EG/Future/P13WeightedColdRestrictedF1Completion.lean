import Erdos64EG.Future.P13WeightedColdRestrictedPrefixStages
import Erdos64EG.Shared.CT10P13LabelAlgebra
import StructuralExhaustion.Graph.InducedPathRestrictedPrefixCompletion

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

abbrev F1Candidate := package.Stage × Fin 13

@[implicit_reducible] noncomputable def f1Candidates :
    FinEnum package.F1Candidate := by
  letI : FinEnum package.Stage := package.profile.stageEnumeration
  exact inferInstance

/-- The literal C153.3 predicate: one stored prefix endpoint has an actual
edge to the displayed anchor-window offset, and the exactly constructed cycle
length is dyadic. -/
def F1At (candidate : package.F1Candidate) : Prop :=
  InducedPathRestrictedPrefixCompletion.CompletionAt package.input
    PowerOfTwoLength candidate.1 candidate.2

noncomputable def f1AtDecidable (candidate : package.F1Candidate) :
    Decidable (package.F1At candidate) := by
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  unfold F1At InducedPathRestrictedPrefixCompletion.CompletionAt
  exact instDecidableAnd

/-- Ordered local scan of exactly path-support-length times thirteen
stage/offset pairs. -/
noncomputable def f1Scan :=
  Core.FiniteSearch.first package.f1Candidates package.F1At
    package.f1AtDecidable

theorem f1_first_hit_sound
    (hit : Core.FiniteSearch.FirstHit
      package.f1Candidates.orderedValues package.F1At) :
    hit.value ∈ package.f1Candidates.orderedValues ∧
      package.F1At hit.value :=
  Core.FiniteSearch.first_hit_sound hit

theorem f1_first_hit_no_earlier
    (hit : Core.FiniteSearch.FirstHit
      package.f1Candidates.orderedValues package.F1At) :
    ∀ candidate ∈ hit.before, ¬package.F1At candidate :=
  Core.FiniteSearch.first_hit_no_earlier hit

/-- Every reported F1 hit is a literal Mathlib simple cycle in the original
counterexample graph and has power-of-two length. -/
noncomputable def f1Cycle
    (hit : Core.FiniteSearch.FirstHit
      package.f1Candidates.orderedValues package.F1At) :
    CycleWithLength ctx.G.object.graph PowerOfTwoLength :=
  InducedPathRestrictedPrefixCompletion.cycleOfCompletion package.input
    PowerOfTwoLength hit.value.1 hit.value.2 hit.holds

/-- Visible work bound: thirteen local adjacency/length tests per stored
prefix descriptor. -/
noncomputable def f1Checks : Nat := package.checks * 13

theorem f1Checks_eq : package.f1Checks = package.checks * 13 := rfl

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
