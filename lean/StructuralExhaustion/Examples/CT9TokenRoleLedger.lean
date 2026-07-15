import StructuralExhaustion.CT9.TokenRoleLedger

namespace StructuralExhaustion.Examples.CT9TokenRoleLedger

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ ↦ True
  rank := fun _ ↦ 0
  BranchState := fun _ ↦ Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def items : Core.OrderedCollection (Fin 6) where
  values := [0, 1, 2, 3, 4, 5]
  nodup := by decide
  decEq := inferInstance

def token (item : Fin 6) : Fin 2 :=
  ⟨item.val % 2, Nat.mod_lt _ (by decide)⟩

def role (item : Fin 6) : Bool := item.val < 3

/-- Six textbook records are partitioned exactly by a two-bin token and a
two-valued role.  This exercises the same product-ledger contract as the
surplus-pair routing without any graph-specific data. -/
example : items.values.length =
    (((CT9.TokenRoleLedger.labels
      (inferInstance : FinEnum (Fin 2))
      (Core.Enumeration.bool)).orderedValues.map fun labelValue ↦
        CT9.fibreCount
          (CT9.TokenRoleLedger.capability problem (Fin 6)
            (inferInstance : FinEnum (Fin 2)) Core.Enumeration.bool token role)
          (CT9.TokenRoleLedger.input
            (capacity := fun _ _ ↦ 0) context items)
          labelValue).sum) :=
  CT9.TokenRoleLedger.noOvercounting
    (inferInstance : FinEnum (Fin 2)) Core.Enumeration.bool token role
    context items

example :
    CT9.fibreCount
      (CT9.TokenRoleLedger.capability problem (Fin 6)
        (inferInstance : FinEnum (Fin 2)) Core.Enumeration.bool token role)
      (CT9.TokenRoleLedger.input (capacity := fun _ _ ↦ 0) context items)
      (0, true) = 2 := by
  native_decide

end StructuralExhaustion.Examples.CT9TokenRoleLedger
