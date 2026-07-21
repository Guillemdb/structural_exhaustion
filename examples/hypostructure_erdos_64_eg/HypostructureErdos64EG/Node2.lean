import Hypostructure.Core.Residual.Decision
import HypostructureErdos64EG.Node1

/-!
# Diagram node 2: exhaustive counterexample decision

The minimum-degree premise is already in the root residual.  Node 2 asks the
paper's exact question and lets Core construct both dependent branches.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Framework query for the unique residual carried by node 1. -/
def node1ResidualQuery :
    Core.Residual.Query Node1Stage (fun _stage => InitialResidual.{u}) :=
  Core.Residual.Query.residual

/-- The exact positive branch of diagram node 2. -/
def IsCounterexample (stage : Node1Stage.{u}) : Prop :=
  let residual := node1ResidualQuery.read stage
  problem.Baseline residual.object ∧ Not (Target residual.object)

/-- The exact negative branch of diagram node 2. -/
def IsNotCounterexample (stage : Node1Stage.{u}) : Prop :=
  Target (node1ResidualQuery.read stage).object

/-- Core-owned exhaustive decision profile for node 2. -/
noncomputable def node2Decision :
    Core.Residual.Decision.Node Node1Stage IsCounterexample
      IsNotCounterexample :=
  Core.Residual.Decision.Node.create
    (fun stage => by
      classical
      exact inferInstanceAs (Decidable (IsCounterexample stage)))
    (fun stage absent => by
      let residual := node1ResidualQuery.read stage
      change Target residual.object
      by_contra avoids
      exact absent ⟨residual.baseline, avoids⟩)

/-- Exact accumulated stage emitted by diagram node 2. -/
abbrev Node2Stage :=
  Core.Residual.Decision.Stage IsCounterexample IsNotCounterexample

/-- Execute node 2 on its literal node-1 predecessor. -/
noncomputable def node2 (previous : Node1Stage.{u}) : Node2Stage.{u} :=
  node2Decision.run previous

@[simp] theorem node2_previous (previous : Node1Stage.{u}) :
    (node2 previous).previous = previous :=
  rfl

/-- Node 2 exposes exactly the two branches in the manuscript. -/
theorem node2_exhaustive (previous : Node1Stage.{u}) :
    match (node2 previous).added with
    | .yesBranch _proof => IsCounterexample previous
    | .noBranch _proof => IsNotCounterexample previous := by
  cases (node2 previous).added with
  | yesBranch proof => exact proof
  | noBranch proof => exact proof

/-- A target certificate forces the exact negative constructor. -/
theorem node2_no_branch_of_target (previous : Node1Stage.{u})
    (target : IsNotCounterexample previous) :
    ∃ proof : IsNotCounterexample previous,
      (node2 previous).added =
        Core.Residual.Decision.Binary.noBranch proof := by
  unfold node2 Core.Residual.Decision.Node.run
  cases decision : node2Decision.yesDecidable previous with
  | isTrue counterexample =>
      exact (counterexample.2 target).elim
  | isFalse absent =>
      exact ⟨node2Decision.no_of_not_yes previous absent, rfl⟩

end HypostructureErdos64EG
