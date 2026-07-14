import EvenCycleExample.Problem
import StructuralExhaustion.Graph.P13FanLabelPacking
import StructuralExhaustion.Graph.P13MarkedFanLabelPacking

namespace EvenCycleExample.P13FanLabelPacking

open StructuralExhaustion

/-!
Non-Erdős transfer of the graph-owned CT9 representative-packing profile.
The target predicate is even cycle length, the family has two explicit
singleton labels, and the branch context remains arbitrary.
-/

def items : Core.OrderedCollection Bool where
  values := [false, true]
  nodup := by decide
  decEq := inferInstance

def attachment : Bool → Graph.InducedPathAttachment.Label 13
  | false => {0}
  | true => {1}

theorem attachment_nonempty (item : Bool) : (attachment item).Nonempty := by
  cases item <;> simp [attachment]

theorem compatible {left right : Bool} (distinct : left ≠ right) :
    Graph.InducedPathAttachment.Compatible 13
      (staticInput Unit).LengthOK 2 (attachment left) (attachment right) := by
  cases left <;> cases right <;>
    simp [attachment, Graph.InducedPathAttachment.Compatible,
      Graph.InducedPathAttachment.crossCycleLength,
      Graph.InducedPathAttachment.positionDistance] at distinct ⊢

noncomputable def profile : Graph.P13FanLabelPacking.Profile Bool where
  LengthOK := (staticInput Unit).LengthOK
  items := items
  attachment := attachment
  nonempty := attachment_nonempty
  compatible := compatible
  acceptsFour := by decide
  acceptsEight := by decide
  acceptsSixteen := by decide

noncomputable def run (context : Core.BranchContext (problem Unit)) :=
  profile.run context

theorem terminal (context : Core.BranchContext (problem Unit)) :
    (run context).execution.terminal = .bounded :=
  (run context).terminal_eq

theorem cardinality (context : Core.BranchContext (problem Unit)) :
    items.values.length ≤ 8 :=
  profile.cardinality_le_eight context

def markedAttachment : Bool → Graph.InducedPathAttachment.Label 13
  | false => {0, 2}
  | true => {1}

theorem markedAttachment_nonempty (item : Bool) :
    (markedAttachment item).Nonempty := by
  cases item <;> simp [markedAttachment]

theorem markedCompatible {left right : Bool} (distinct : left ≠ right) :
    Graph.InducedPathAttachment.Compatible 13
      (staticInput Unit).LengthOK 2
      (markedAttachment left) (markedAttachment right) := by
  cases left <;> cases right <;>
    simp [markedAttachment, Graph.InducedPathAttachment.Compatible,
      Graph.InducedPathAttachment.crossCycleLength,
      Graph.InducedPathAttachment.positionDistance] at distinct ⊢

noncomputable def markedBase : Graph.P13FanLabelPacking.Profile Bool where
  LengthOK := (staticInput Unit).LengthOK
  items := items
  attachment := markedAttachment
  nonempty := markedAttachment_nonempty
  compatible := markedCompatible
  acceptsFour := by decide
  acceptsEight := by decide
  acceptsSixteen := by decide

noncomputable def markedProfile :
    Graph.P13MarkedFanLabelPacking.Profile markedBase where
  distinguished := false
  distinguished_mem := by simp [markedBase, items]
  first := 0
  second := 2
  first_mem := by simp [markedBase, markedAttachment]
  second_mem := by simp [markedBase, markedAttachment]
  positions_distinct := by decide

noncomputable def markedRun (context : Core.BranchContext (problem Unit)) :=
  markedProfile.run context

theorem markedTerminal (context : Core.BranchContext (problem Unit)) :
    (markedRun context).execution.terminal = .bounded :=
  (markedRun context).terminal_eq

theorem markedCardinality (context : Core.BranchContext (problem Unit)) :
    items.values.length ≤ 7 :=
  markedProfile.cardinality_le_seven context

end EvenCycleExample.P13FanLabelPacking
