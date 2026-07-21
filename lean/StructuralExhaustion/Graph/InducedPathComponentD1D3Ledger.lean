import StructuralExhaustion.Core.FiniteCodeCollision
import StructuralExhaustion.Graph.InducedPathComponentD1D3Observation

namespace StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger

open StructuralExhaustion
open InducedPathColdCorridor
open InducedPathColdSkeleton
open InducedPathComponentBoundarySchedule
open InducedPathComponentD1D3Observation

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Cyclic D1--D3 ledger on one actual component schedule

The input retains one already computed component schedule and a proved
non-bridge fact for every literal stub in that schedule.  Each schedule entry
is re-anchored, its true cyclic `List.next` successor is retained, and one
declared-order BFS-tree connector is projected to
`State 13 13 (Fin 0)`.

The deterministic collision scan stops at equality of these coarse states.
It does not compare D4--D7 responses and does not execute CT8 removal.
-/

/-- Exact structural input for all cyclic connectors of one component. -/
structure Input (object : FiniteObject V) where
  base : InducedPathComponentBoundarySchedule.Input object
  notBridge : ∀ stub : BoundaryStub object,
    stub ∈ incidentStubs base →
    ¬object.graph.IsBridge
      (CubicStub.dart { token := stub.token, cubic := stub.cubic }).edge

variable (input : Input object)

abbrev Stub := {stub : BoundaryStub object //
  stub ∈ incidentStubs input.base}

/-- The exact inherited incident-stub order, with membership proofs attached. -/
noncomputable def stubs : List (Stub input) :=
  (incidentStubs input.base).attach

theorem stubs_length : (stubs input).length = (incidentStubs input.base).length := by
  simp [stubs]

theorem stubs_nodup : (stubs input).Nodup := by
  exact (incidentStubs_nodup input.base).attach

noncomputable def anchorStub : Stub input :=
  ⟨input.base.anchor, anchor_mem_incidentStubs input.base⟩

/-- Re-anchor the structural producer at one actual schedule entry. -/
noncomputable def connectorInput (stub : Stub input) :
    InducedPathComponentBoundarySchedule.Input object where
  anchor := stub.1
  notBridge := input.notBridge stub.1 stub.2

theorem connectorInput_anchor :
    connectorInput input (anchorStub input) = input.base := by
  cases input
  rfl

/-- Re-anchoring changes only the root certificate: the complete stored
incident schedule is literally the same filtered token list. -/
theorem connector_schedule_eq (stub : Stub input) :
    incidentStubs (connectorInput input stub) = incidentStubs input.base := by
  classical
  unfold incidentStubs
  apply List.filter_congr
  intro candidate _candidateMem
  rw [decide_eq_decide,
    mem_componentVertices_iff, mem_componentVertices_iff]
  have stubSame : component stub.1 = component input.base.anchor :=
    (mem_incidentStubs_iff input.base stub.1).mp stub.2
  change component candidate = component stub.1 ↔
    component candidate = component input.base.anchor
  rw [stubSame]

/-- Every row uses the true cyclic successor in the original node-170 list. -/
theorem connector_successor_eq (stub : Stub input) :
    successor (connectorInput input stub) =
      @List.next _ (boundaryStubs object).decEq
        (incidentStubs input.base) stub.1 stub.2 := by
  letI : DecidableEq (BoundaryStub object) := (boundaryStubs object).decEq
  unfold successor
  change (incidentStubs (connectorInput input stub)).next stub.1 _ =
    (incidentStubs input.base).next stub.1 _
  simp only [List.next_eq_getElem]
  simp [connector_schedule_eq input stub]

/-- One genuine D1--D3 observation row. -/
noncomputable def observation (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (stub : Stub input) :=
  InducedPathComponentD1D3Observation.run (connectorInput input stub)
    LengthOK lengthOKDecidable

theorem anchor_observation_eq (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (observation input LengthOK lengthOKDecidable (anchorStub input)).value =
      (InducedPathComponentD1D3Observation.run input.base LengthOK
        lengthOKDecidable).value := by
  unfold observation
  rw [connectorInput_anchor input]

theorem observation_boundaryDegree_zero (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (stub : Stub input) :
    (observation input LengthOK lengthOKDecidable stub).value.boundaryDegree 0 =
      Core.FixedTwoBoundaryCutState.capDegree
        (object.degree stub.1.neighbor) :=
  InducedPathComponentD1D3Observation.boundaryDegree_zero
    (connectorInput input stub) LengthOK lengthOKDecidable

theorem observation_windowOffset_zero (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (stub : Stub input) :
    (observation input LengthOK lengthOKDecidable stub).value.windowOffset 0 =
      stub.1.offset :=
  InducedPathComponentD1D3Observation.windowOffset_zero
    (connectorInput input stub) LengthOK lengthOKDecidable

theorem observation_windowOffset_one (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (stub : Stub input) :
    (observation input LengthOK lengthOKDecidable stub).value.windowOffset 1 =
      (InducedPathComponentBoundarySchedule.twoStubComponent
        (connectorInput input stub)).successor.offset :=
  InducedPathComponentD1D3Observation.windowOffset_one
    (connectorInput input stub) LengthOK lengthOKDecidable

theorem observation_missing_d4_d7 (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (stub : Stub input) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data (connectorInput input stub))
      (InducedPathComponentD1D3Observation.canonicalPath
        (connectorInput input stub))) :=
  ⟨(observation input LengthOK lengthOKDecidable stub).missing⟩

abbrev State := Core.FixedTwoBoundaryCutState.State 13 13 (Fin 0)

/-- A stored row keeps its exact schedule entry beside its computed state. -/
abbrev Row (LengthOK : Nat → Prop)
    (_lengthOKDecidable : DecidablePred LengthOK) := Stub input × State

noncomputable def rowState (anchorState : State)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    (stub : Stub input) : State := by
  letI : DecidableEq (BoundaryStub object) := (boundaryStubs object).decEq
  exact if stub.1 = input.base.anchor then anchorState
    else (observation input LengthOK lengthOKDecidable stub).value

theorem rowState_anchor (anchorState : State)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    rowState input anchorState LengthOK lengthOKDecidable (anchorStub input) =
      anchorState := by
  simp [rowState, anchorStub]

theorem rowState_nonanchor (anchorState : State)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    (stub : Stub input) (different : stub.1 ≠ input.base.anchor) :
    rowState input anchorState LengthOK lengthOKDecidable stub =
      (observation input LengthOK lengthOKDecidable stub).value := by
  simp [rowState, different]

noncomputable def rows (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    List (Row input LengthOK lengthOKDecidable) :=
  (stubs input).map fun stub =>
    (stub, rowState input anchorState LengthOK lengthOKDecidable stub)

theorem rows_length (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (rows input anchorState LengthOK lengthOKDecidable).length =
      (incidentStubs input.base).length := by
  simp [rows, stubs]

theorem rows_nodup (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    (rows input anchorState LengthOK lengthOKDecidable).Nodup := by
  apply (stubs_nodup input).map
  intro left right equal
  exact congrArg Prod.fst equal

/-- Exact cardinality used only as a proof bound; the collision runner never
enumerates this code universe. -/
theorem stateCard : Fintype.card State = 4 ^ 2 * 13 ^ 2 * 2 ^ 13 := by
  rw [Core.FixedTwoBoundaryCutState.state_card]
  norm_num

abbrev Collision (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :=
  Core.FiniteCodeCollision.OrderedCollision Prod.snd
    (rows input anchorState LengthOK lengthOKDecidable)

/-- Full coarse repetition residual.  Its two rows retain the exact schedule
entries; `connectorInput`, `canonicalPath`, and `observation` recover both
computed connectors and their typed missing-D4--D7 residuals without search. -/
structure Repetition (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) where
  collision : Collision input anchorState LengthOK lengthOKDecidable
  distinctRows : collision.first ≠ collision.second
  distinct : collision.first.1 ≠ collision.second.1
  sameState : collision.first.2 = collision.second.2

namespace Repetition

variable {input} {anchorState : State} {LengthOK : Nat → Prop}
variable {lengthOKDecidable : DecidablePred LengthOK}

noncomputable abbrev firstInput
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :=
  connectorInput input repetition.collision.first.1

noncomputable abbrev secondInput
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :=
  connectorInput input repetition.collision.second.1

noncomputable abbrev firstPath
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :=
  InducedPathComponentD1D3Observation.canonicalPath repetition.firstInput

noncomputable abbrev secondPath
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :=
  InducedPathComponentD1D3Observation.canonicalPath repetition.secondInput

theorem first_path_isPath
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :
    repetition.firstPath.path.IsPath := repetition.firstPath.isPath

theorem second_path_isPath
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :
    repetition.secondPath.path.IsPath := repetition.secondPath.isPath

theorem first_missing_d4_d7
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data repetition.firstInput)
      repetition.firstPath) :=
  ⟨(observation input LengthOK lengthOKDecidable
    repetition.collision.first.1).missing⟩

theorem second_missing_d4_d7
    (repetition : Repetition input anchorState LengthOK lengthOKDecidable) :
    Nonempty (TwoStubComponent.MissingD4D7Reconstruction
      (InducedPathComponentD1D3Observation.data repetition.secondInput)
      repetition.secondPath) :=
  ⟨(observation input LengthOK lengthOKDecidable
    repetition.collision.second.1).missing⟩

end Repetition

/-- The complete local result: a repeated stored state or a certified
schedule-length bound by the exact finite code universe. -/
inductive Result (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) where
  | repeated (repetition : Repetition input anchorState LengthOK lengthOKDecidable)
  | bounded (codesNodup :
      ((rows input anchorState LengthOK lengthOKDecidable).map Prod.snd).Nodup)
      (lengthLe : (incidentStubs input.base).length ≤ Fintype.card State)

/-- Deterministic first coarse-code collision scan. -/
noncomputable def run (anchorState : State) (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) :
    Result input anchorState LengthOK lengthOKDecidable := by
  classical
  cases decision : Core.FiniteCodeCollision.decideWithDecEq Prod.snd
      (rows input anchorState LengthOK lengthOKDecidable) with
  | collision collision =>
      exact .repeated {
        collision := collision
        distinctRows := collision.first_ne_second_of_nodup
          (rows_nodup input anchorState LengthOK lengthOKDecidable)
        distinct := by
          intro sameStub
          apply collision.first_ne_second_of_nodup
            (rows_nodup input anchorState LengthOK lengthOKDecidable)
          obtain ⟨firstStub, firstMem, firstExact⟩ :=
            List.mem_map.mp collision.first_mem
          obtain ⟨secondStub, secondMem, secondExact⟩ :=
            List.mem_map.mp collision.second_mem
          rw [← firstExact, ← secondExact] at sameStub ⊢
          cases sameStub
          rfl
        sameState := collision.code_eq
      }
  | unique codesNodup =>
      exact Result.bounded codesNodup (by
        rw [← rows_length input anchorState LengthOK lengthOKDecidable,
          ← List.length_map]
        exact codesNodup.length_le_card)

/-- Per-row structural work: build its literal schedule/successor/BFS connector
and then materialize its two degree rows and thirteen target bits. -/
noncomputable def rowChecks (stub : Stub input) : Nat :=
  InducedPathComponentBoundarySchedule.visibleChecks
      (connectorInput input stub) +
    InducedPathComponentD1D3Observation.visibleChecks
      (connectorInput input stub)

/-- Exact visible upper ledger.  One stored-state equality checks at most two
degree coordinates, two window offsets, and thirteen target bits.  The scan
compares at most every ordered pair and never enumerates the code universe. -/
noncomputable def visibleChecks : Nat :=
  ((stubs input).map (rowChecks input)).sum +
    17 * (stubs input).length ^ 2

noncomputable def localScale : Nat :=
  1 + (stubs input).length +
    ((stubs input).map fun stub =>
      InducedPathComponentBoundarySchedule.localScale
        (connectorInput input stub)).sum + object.input.vertices.card

theorem visibleChecks_polynomial :
    visibleChecks input ≤ 100 * localScale input ^ 4 := by
  let scale := localScale input
  have scalePos : 1 ≤ scale := by
    dsimp [scale, localScale]
    omega
  have stubsLe : (stubs input).length ≤ scale := by
    dsimp [scale, localScale]
    omega
  have verticesLe : object.input.vertices.card ≤ scale := by
    dsimp [scale, localScale]
    omega
  have eachScaleLe : ∀ stub ∈ stubs input,
      InducedPathComponentBoundarySchedule.localScale
          (connectorInput input stub) ≤ scale := by
    intro stub member
    dsimp [scale, localScale]
    have termLe :
        InducedPathComponentBoundarySchedule.localScale
            (connectorInput input stub) ≤
          ((stubs input).map fun entry =>
            InducedPathComponentBoundarySchedule.localScale
              (connectorInput input entry)).sum := by
      apply List.le_sum_of_mem
      exact List.mem_map_of_mem member
    omega
  have scaleLeCube : scale ≤ scale ^ 3 := by
    calc
      scale = scale * 1 := by omega
      _ ≤ scale * (scale * scale) := by
        exact Nat.mul_le_mul_left scale
          (Nat.mul_self_le_mul_self scalePos)
      _ = scale ^ 3 := by ring
  have rowLe : ∀ stub ∈ stubs input,
      rowChecks input stub ≤ 80 * scale ^ 3 := by
    intro stub member
    have structural :=
      InducedPathComponentBoundarySchedule.visibleChecks_polynomial
        (connectorInput input stub)
    have state :=
      InducedPathComponentD1D3Observation.visibleChecks_linear
        (connectorInput input stub)
    have localLe := eachScaleLe stub member
    have cubeLe := Nat.pow_le_pow_left localLe 3
    have stateLe :
        InducedPathComponentD1D3Observation.visibleChecks
            (connectorInput input stub) ≤ 30 * scale := by
      calc
        _ ≤ 15 * (object.input.vertices.card + 1) := state
        _ ≤ 15 * (scale + scale) := by omega
        _ = 30 * scale := by ring
    unfold rowChecks
    calc
      _ ≤ 50 * scale ^ 3 + 30 * scale :=
        Nat.add_le_add (structural.trans (Nat.mul_le_mul_left 50 cubeLe)) stateLe
      _ ≤ 50 * scale ^ 3 + 30 * scale ^ 3 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 30 scaleLeCube) _
      _ = 80 * scale ^ 3 := by ring
  have sumLe : ((stubs input).map (rowChecks input)).sum ≤
      (stubs input).length * (80 * scale ^ 3) := by
    calc
      _ ≤ ((stubs input).map fun _stub => 80 * scale ^ 3).sum := by
        apply List.sum_le_sum
        exact rowLe
      _ = (stubs input).length * (80 * scale ^ 3) := by
        simp [Nat.mul_comm]
  unfold visibleChecks
  have sumPolynomial :
      (stubs input).length * (80 * scale ^ 3) ≤ 80 * scale ^ 4 := by
    calc
      _ ≤ scale * (80 * scale ^ 3) := Nat.mul_le_mul_right _ stubsLe
      _ = 80 * scale ^ 4 := by ring
  have squareLe : (stubs input).length ^ 2 ≤ scale ^ 2 :=
    Nat.pow_le_pow_left stubsLe 2
  have squarePolynomial : 17 * (stubs input).length ^ 2 ≤
      20 * scale ^ 4 := by
    have : scale ^ 2 ≤ scale ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc
      _ ≤ 17 * scale ^ 2 := Nat.mul_le_mul_left 17 squareLe
      _ ≤ 17 * scale ^ 4 := Nat.mul_le_mul_left 17 this
      _ ≤ 20 * scale ^ 4 := by omega
  calc
    _ ≤ (stubs input).length * (80 * scale ^ 3) +
        17 * (stubs input).length ^ 2 := Nat.add_le_add sumLe (le_refl _)
    _ ≤ 80 * scale ^ 4 + 20 * scale ^ 4 :=
      Nat.add_le_add sumPolynomial squarePolynomial
    _ = 100 * scale ^ 4 := by ring

end StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger
