import StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

namespace StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

open StructuralExhaustion
open InducedPathColdSkeleton
open InducedPathComponentBoundarySchedule

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# One D1--D3 observation from a component boundary schedule

This module consumes one exact component boundary schedule and its computed
declared-order BFS path.  It records the two literal boundary degrees, the two
literal induced-path window offsets, and the connector length, then projects
those observations to one `FixedTwoBoundaryCutState.State 13 13 (Fin 0)`.

The empty coordinate type records that no D4--D7 response has been supplied.
Accordingly the result retains `MissingD4D7Reconstruction`.  It is one state,
not a state sequence or a repetition theorem.
-/

variable (input : InducedPathComponentBoundarySchedule.Input object)

noncomputable abbrev data := twoStubComponent input

/-- A rank which singles out the already computed BFS path without scanning
any path family. -/
noncomputable def bfsPathTieBreak :
    TwoStubComponent.PathTieBreak (data input) := by
  classical
  exact { rank := fun candidate =>
    if candidate = componentPath input then 0 else 1 }

/-- The exact BFS path packaged for the existing observation interface.  The
tie-break proof compares only a supplied candidate with the computed path. -/
noncomputable def canonicalPath :
    TwoStubComponent.CanonicalComponentPath
      (data input) (bfsPathTieBreak input) where
  path := componentPath input
  isPath := componentPath_isPath input
  shortest := componentPath_shortest input
  declaredFirst := by
    intro candidate _candidatePath _candidateShortest
    simp [bfsPathTieBreak]

/-- Genuine two-boundary observations owned by the computed node-170 data. -/
noncomputable def observations :
    Core.FixedTwoBoundaryCutState.PrefixObservations 13 Unit :=
  (data input).observations (canonicalPath input)

/-- The unique empty-coordinate response. -/
def emptyLocalProjection :
    Core.FixedTwoBoundaryCutState.LocalProjection Unit (Fin 0) where
  response := fun _ coordinate => Fin.elim0 coordinate

/-- Exactly one normalized D1--D3 state. -/
noncomputable def state (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    Core.FixedTwoBoundaryCutState.State 13 13 (Fin 0) :=
  Core.FixedTwoBoundaryCutState.project LengthOK lengthOKDecidable
    (observations input) emptyLocalProjection ()

/-- Honest stopping output after the one structural projection. -/
structure OneStateResidual (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) where
  value : Core.FixedTwoBoundaryCutState.State 13 13 (Fin 0)
  valueExact : value = state input LengthOK lengthOKDecidable
  missing : TwoStubComponent.MissingD4D7Reconstruction
    (data input) (canonicalPath input)

/-- Execute the fixed projection. -/
noncomputable def run (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    OneStateResidual input LengthOK lengthOKDecidable where
  value := state input LengthOK lengthOKDecidable
  valueExact := rfl
  missing := {}

theorem boundaryDegree_zero (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (run input LengthOK lengthOKDecidable).value.boundaryDegree 0 =
      Core.FixedTwoBoundaryCutState.capDegree
        (object.degree (data input).anchor.neighbor) := rfl

theorem boundaryDegree_one (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (run input LengthOK lengthOKDecidable).value.boundaryDegree 1 =
      Core.FixedTwoBoundaryCutState.capDegree
        (object.degree (data input).successor.neighbor) := rfl

theorem windowOffset_zero (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (run input LengthOK lengthOKDecidable).value.windowOffset 0 =
      (data input).anchor.offset := rfl

set_option maxHeartbeats 800000 in
theorem windowOffset_one (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (run input LengthOK lengthOKDecidable).value.windowOffset 1 =
      (data input).successor.offset := by
  change (if (1 : Core.FixedTwoBoundaryCutState.BoundaryRole) = 0 then
      (data input).anchor.offset else (data input).successor.offset) = _
  simp

theorem targetResponse_eq (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (offset : Core.FixedTwoBoundaryCutState.TargetOffset 13) :
    (run input LengthOK lengthOKDecidable).value.targetResponse offset =
      decide (LengthOK ((componentPath input).length + offset.val)) := rfl

theorem localResponse_empty (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    (coordinate : Fin 0) :
    (run input LengthOK lengthOKDecidable).value.localResponse coordinate =
      Fin.elim0 coordinate := by
  exact Fin.elim0 coordinate

/-- Materializing the state inspects two degree rows and thirteen fixed target
offsets.  The offsets, stored connector length, and empty local response add no
ambient scan. -/
def visibleChecks (_input : InducedPathComponentBoundarySchedule.Input object) : Nat :=
  2 * object.input.vertices.card + 13

theorem visibleChecks_eq :
    visibleChecks input = 2 * object.input.vertices.card + 13 := rfl

theorem visibleChecks_linear :
    visibleChecks input ≤ 15 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.InducedPathComponentD1D3Observation
