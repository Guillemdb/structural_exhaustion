import StructuralExhaustion.CT9.ExactLedger

namespace StructuralExhaustion.Examples.CT9ExactLedger

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def items : Core.OrderedCollection (Fin 5) where
  values := [0, 1, 2, 3, 4]
  nodup := by decide
  decEq := inferInstance

def parity (item : Fin 5) : Fin 2 :=
  ⟨item.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Five textbook objects are partitioned exactly by parity; no object is
lost and no object is counted twice. -/
example : items.values.length =
    ((inferInstance : FinEnum (Fin 2)).orderedValues.map fun label =>
      CT9.fibreCount
        (CT9.ExactLedger.capability problem (Fin 5) (Fin 2) inferInstance
          parity)
        (CT9.ExactLedger.input (capacity := fun _ => 0) context items)
        label).sum :=
  CT9.ExactLedger.noOvercounting inferInstance
    parity
    context items

end StructuralExhaustion.Examples.CT9ExactLedger
