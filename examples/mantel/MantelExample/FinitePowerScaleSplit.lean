import MantelExample.FiniteStateEntropyBookkeeping
import StructuralExhaustion.Core.FinitePowerScaleSplit

namespace MantelExample.FinitePowerScaleSplit

open StructuralExhaustion

/-!
# Exact power-scale split on the concrete Mantel `C₅`

The base and support are the vertex count of the actual concrete cycle, and
the state count is the exact collection of its five supplied vertex states.
The shared Core runner makes one arithmetic comparison; it never enumerates
graphs, subsets, functions, or a Boolean realization family.
-/

/-- The node-50 scale, instantiated on graph data already verified by the
external Mantel example. -/
def profile : Core.FinitePowerScaleSplit.Profile where
  base := ConcreteC5.object.input.vertices.card
  supportSize :=
    FiniteStateEntropyBookkeeping.profile.supportSize
  stateCount :=
    FiniteStateEntropyBookkeeping.profile.stateCount
  scale := 10

/-- Proof-carrying execution of the shared constant-work runner. -/
def stage : profile.VerifiedStage :=
  profile.verifiedStage

/-- The concrete Mantel data lie on the upper branch of the exact split. -/
theorem upper_bound :
    profile.base ^ profile.supportSize ≤ profile.stateCount ^ profile.scale := by
  native_decide

/-- The concrete upper branch consumes the shared Core logarithmic-budget
theorem on the same five supplied `C₅` vertex states. -/
theorem upper_logb_budget :
    (profile.supportSize : ℝ) * Real.logb 2 profile.base ≤
      (profile.scale : ℝ) * Real.logb 2 profile.stateCount :=
  profile.logb_budget_of_upper
    (by
      change 0 < FiniteStateEntropyBookkeeping.profile.stateCount
      rw [FiniteStateEntropyBookkeeping.stateCount_exact]
      decide)
    upper_bound

/-- The runner returns the upper constructor on this actual graph input. -/
theorem outcome_upper :
    ∃ bound, stage.outcome = .upper bound := by
  refine ⟨upper_bound, ?_⟩
  change profile.run = .upper upper_bound
  unfold Core.FinitePowerScaleSplit.Profile.run
  split
  · congr
  · rename_i notBound
    exact (notBound upper_bound).elim

/-- The stage retains the exhaustive two-way arithmetic theorem. -/
theorem exhaustive :
    profile.base ^ profile.supportSize ≤ profile.stateCount ^ profile.scale ∨
      profile.stateCount ^ profile.scale < profile.base ^ profile.supportSize :=
  stage.total

/-- The shared execution makes exactly one comparison. -/
theorem work_exact : profile.checks = 1 :=
  stage.work

/-- This transfer is tied to the same concrete graph object whose source
theorem proves triangle-freeness. -/
theorem source_triangleFree : ConcreteC5.object.graph.CliqueFree 3 :=
  ConcreteC5.triangleFree

/-- The same source object is an input to the external package's actual
Mantel theorem, rather than a detached arithmetic fixture. -/
theorem source_mantel_bound : Target ConcreteC5.object :=
  ConcreteC5.mantel_bound

/-- A second fixed-scale fixture uses the actual neighborhood state count at
vertex zero.  It exercises the strict reverse branch without inventing a
numerical toy input. -/
def neighborhoodProfile : Core.FinitePowerScaleSplit.Profile where
  base := ConcreteC5.object.input.vertices.card
  supportSize := ConcreteC5.object.input.vertices.card
  stateCount := ConcreteC5.object.degree (0 : ConcreteC5.Vertex)
  scale := 10

def neighborhoodStage : neighborhoodProfile.VerifiedStage :=
  neighborhoodProfile.verifiedStage

theorem neighborhood_lower_bound :
    neighborhoodProfile.stateCount ^ neighborhoodProfile.scale <
      neighborhoodProfile.base ^ neighborhoodProfile.supportSize := by
  native_decide

theorem neighborhood_outcome_lower :
    ∃ strict, neighborhoodStage.outcome = .lower strict := by
  refine ⟨neighborhood_lower_bound, ?_⟩
  change neighborhoodProfile.run = .lower neighborhood_lower_bound
  unfold Core.FinitePowerScaleSplit.Profile.run
  split
  · rename_i bound
    exact (Nat.not_lt_of_ge bound neighborhood_lower_bound).elim
  · congr

end MantelExample.FinitePowerScaleSplit
