import HypostructureErdos64EG.Node50
import Hypostructure.Core.Finite.Partition

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node51PartitionContract (Previous : Type u) (Item : Type v) where
  schedule : Previous -> Core.Finite.Enumeration Item
  predicate : Previous -> Item -> Prop
  decidePredicate : ∀ previous item,
    Decidable (predicate previous item)

abbrev Node51PartitionResult (contract : Node51PartitionContract Previous Item)
    (previous : Previous) :=
  Core.Finite.Partition.Result (contract.schedule previous)
    (contract.predicate previous)

noncomputable def node51Partition
    (contract : Node51PartitionContract Previous Item) (previous : Previous) :
    Node51PartitionResult contract previous :=
  Core.Finite.Partition.run (contract.schedule previous)
    (contract.predicate previous)
    (contract.decidePredicate previous)

abbrev Node51Stage (contract : Node50Contract Previous)
    (Bits : Node50Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node50Stage contract) Bits

noncomputable def node51 (contract : Node50Contract Previous)
    (Bits : Node50Stage contract -> Type v)
    (previous : Node50Stage contract) (bits : Bits previous) :
    Node51Stage contract Bits :=
  Core.Residual.Ledger.extend previous bits

end HypostructureErdos64EG
