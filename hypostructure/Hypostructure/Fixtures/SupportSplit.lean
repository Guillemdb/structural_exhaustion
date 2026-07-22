import Hypostructure.Core.SupportSplit

/-!
# Domain-neutral support-split fixture

The carrier is intentionally not a graph or PDE object.  It exercises the
exact schedule, negative source contract, exhaustive high/low outcome, and
predecessor-query projection.
-/

namespace Hypostructure.Fixtures.SupportSplit

open Hypostructure.Core.Finite
open Hypostructure.Core.Residual
open Hypostructure.Core.SupportSplit

instance : HasResidual Unit Unit where
  residual := id

def source : Source Nat where
  core := {0, 1}
  cells := Enumeration.ofNodupList [0, 1] (by simp)
  cells_toFinset := by
    ext value
    simp [Enumeration.ofNodupList, Enumeration.toFinset]
  charge := fun value => if value = 0 then -2 else 0
  negative := by norm_num [Enumeration.ofNodupList]

def split : HighSplit Nat source where
  high := fun value => value = 1
  high_decidable := fun _value => inferInstance

theorem highValues_eq : highValues split = [1] := by
  norm_num [highValues, split, source, Enumeration.ofNodupList]

theorem outcome_exhaustive :
    (∃ value member, execute split = .high value member) ∨
      (∃ none, execute split = .low none) :=
  outcome_cases (execute split)

def sourceQuery : Query Unit (fun _unit => Source Nat) :=
  (Query.residual (Source := Unit) (Residual := Unit)).map
    (fun _unit _value => source)

def splitQuery : Query Unit (fun _unit =>
    HighSplit Nat (sourceQuery.read _unit)) :=
  sourceQuery.map (fun _unit _value => split)

def stage := QuerySurface.stageNode sourceQuery splitQuery

theorem stage_preserves_previous :
    (stage.run ()).previous = () :=
  StageNode.run_previous stage ()

#print axioms highValues_eq
#print axioms outcome_exhaustive
#print axioms stage_preserves_previous

end Hypostructure.Fixtures.SupportSplit
