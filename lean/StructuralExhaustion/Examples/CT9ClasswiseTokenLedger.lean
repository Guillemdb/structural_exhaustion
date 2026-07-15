import StructuralExhaustion.CT9.ClasswiseTokenLedger

namespace StructuralExhaustion.Examples.CT9ClasswiseTokenLedger

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

def token (item : Fin 5) : Fin 2 :=
  ⟨item.val % 2, Nat.mod_lt _ (by decide)⟩

def role (item : Fin 5) : Bool := item.val < 2

/-- A five-record textbook ledger with two tokens, two roles, and one unit of
capacity in every token class. -/
noncomputable def profile : CT9.ClasswiseTokenLedger.Profile problem where
  Item := Fin 5
  Token := Fin 2
  Role := Bool
  Class := Fin 2
  tokens := inferInstance
  roles := Core.Enumeration.bool
  classOf := id
  token := token
  role := role
  classCapacity := fun _ => 1

example : profile.totalCapacity = 4 := by decide

example : items.values.length =
    (profile.labels.orderedValues.map fun label =>
      CT9.fibreCount profile.capability (profile.input context items) label).sum :=
  profile.exactPartition context items

/-- The same executable decision contract used by the graph specialization:
the five records either return an actual overloaded fibre or the literal
aggregate capacity inequality. -/
noncomputable def decision : profile.Decision context items :=
  profile.decide context items

example : profile.checks items = 20 := by decide

end StructuralExhaustion.Examples.CT9ClasswiseTokenLedger
