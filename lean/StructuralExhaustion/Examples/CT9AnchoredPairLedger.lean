import StructuralExhaustion.CT9.AnchoredPairLedger

namespace StructuralExhaustion.Examples.CT9AnchoredPairLedger

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ ↦ True
  rank := fun _ ↦ 0
  BranchState := fun _ ↦ Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

@[implicit_reducible]
def students : FinEnum (Fin 4) := inferInstance

def zeroStudent :
    (CT9.AnchoredPairLedger.capability problem students).Label := by
  change Fin 4
  exact 0

/-- The six textbook pairs are partitioned by their earlier student. -/
example :
    (CT9.AnchoredPairLedger.pairs students).orderedValues.length =
      (students.orderedValues.map fun student ↦
        CT9.fibreCount
          (CT9.AnchoredPairLedger.capability problem students)
          (CT9.AnchoredPairLedger.input (capacity := fun _ ↦ 0) context)
          student).sum :=
  CT9.AnchoredPairLedger.noOvercounting students context

example : (CT9.AnchoredPairLedger.pairs students).card = 6 := by
  native_decide

/-- Two pairs charged to student zero have the same canonical first endpoint. -/
example (left right : CT9.AnchoredPairLedger.Pair students)
    (leftMember : left ∈ CT9.fibre
      (CT9.AnchoredPairLedger.capability problem students)
      (CT9.AnchoredPairLedger.input (capacity := fun _ ↦ 0) context)
      zeroStudent)
    (rightMember : right ∈ CT9.fibre
      (CT9.AnchoredPairLedger.capability problem students)
      (CT9.AnchoredPairLedger.input (capacity := fun _ ↦ 0) context)
      zeroStudent) :
    CT9.AnchoredPairLedger.anchor left =
      CT9.AnchoredPairLedger.anchor right :=
  CT9.AnchoredPairLedger.same_anchor_of_mem_fibre context
    leftMember rightMember

end StructuralExhaustion.Examples.CT9AnchoredPairLedger
