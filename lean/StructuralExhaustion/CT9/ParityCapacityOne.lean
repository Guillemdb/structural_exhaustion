import StructuralExhaustion.Core.Parity
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.CT9.Theorems

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem

/-- Minimal authored data for the parity/capacity-one capability profile. -/
structure ParityCapacityOneSpec (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Type uItem
  rank : Item → Nat

/-- Canonical two-box pigeonhole capability.  Items are labelled by the
parity of an application-supplied natural rank, and each parity class has
capacity one. -/
def parityCapacityOne
    (P : Core.Problem.{uAmbient, uBranch}) (Item : Type uItem)
    (rank : Item → Nat) : Capability P where
  Item := Item
  Label := Bool
  labels := Core.Enumeration.bool
  label := fun item => Core.Parity.label (rank item)
  capacity := fun _label => 1

namespace ParityCapacityOneSpec

/-- Generate the complete CT9 capability from the two profile fields. -/
def capability
    {P : Core.Problem.{uAmbient, uBranch}}
    (profile : ParityCapacityOneSpec.{uAmbient, uBranch, uItem} P) :
    Capability P :=
  parityCapacityOne P profile.Item profile.rank

end ParityCapacityOneSpec

@[simp] theorem totalCapacity_parityCapacityOne
    (P : Core.Problem.{uAmbient, uBranch}) (Item : Type uItem)
    (rank : Item → Nat) :
    totalCapacity (parityCapacityOne P Item rank) = 2 :=
  rfl

/-- Domain-independent payload of the three-items/two-parity-classes
pigeonhole principle. -/
structure SameParityPair
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    (rank : Item → Nat)
    (input : Input (parityCapacityOne P Item rank)) where
  first : Item
  second : Item
  first_mem : first ∈ input.items.values
  second_mem : second ∈ input.items.values
  distinct : first ≠ second
  same_parity : rank first % 2 = rank second % 2

/-- Exact CT9 run forced by the capacity-one parity principle. -/
structure ParityCapacityOneRun
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    (rank : Item → Nat)
    (input : Input (parityCapacityOne P Item rank)) where
  overloaded : OverloadedRun (parityCapacityOne P Item rank) input

namespace ParityCapacityOneRun

def execution
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {rank : Item → Nat}
    {input : Input (parityCapacityOne P Item rank)}
    (bundle : ParityCapacityOneRun rank input) :
    ExecutionResult (parityCapacityOne P Item rank) input :=
  bundle.overloaded.execution

def residual
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {rank : Item → Nat}
    {input : Input (parityCapacityOne P Item rank)}
    (bundle : ParityCapacityOneRun rank input) :
    OverloadResidual (parityCapacityOne P Item rank) input :=
  bundle.overloaded.residual

theorem terminal_eq
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {rank : Item → Nat}
    {input : Input (parityCapacityOne P Item rank)}
    (bundle : ParityCapacityOneRun rank input) :
    bundle.execution.terminal = .overloaded :=
  bundle.overloaded.terminal_eq

theorem trace_eq
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {rank : Item → Nat}
    {input : Input (parityCapacityOne P Item rank)}
    (bundle : ParityCapacityOneRun rank input) :
    bundle.execution.trace =
      [.entry, .partition, .overload, .overloadedTerminal] :=
  bundle.overloaded.trace_eq

/-- Extract the same-parity pair carried by the exact overloaded run. -/
def pair
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    {rank : Item → Nat}
    {input : Input (parityCapacityOne P Item rank)}
    (bundle : ParityCapacityOneRun rank input) :
    SameParityPair rank input := by
  let pair := OverloadedRun.sameLabelPairOfCapacityOne
    (parityCapacityOne P Item rank) input bundle.overloaded (by rfl)
  exact {
    first := pair.first
    second := pair.second
    first_mem := pair.first_mem
    second_mem := pair.second_mem
    distinct := pair.distinct
    same_parity := Core.Parity.mod_two_eq_of_label_eq pair.labels_eq
  }

end ParityCapacityOneRun

/-- Three distinct active items force the exact CT9 parity-capacity-one run
to overload and expose two distinct items of equal parity. -/
def runParityCapacityOneOfThreeLeCardinality
    {P : Core.Problem.{uAmbient, uBranch}} {Item : Type uItem}
    (rank : Item → Nat)
    (input : Input (parityCapacityOne P Item rank))
    (three : 3 ≤ input.items.values.length) :
    ParityCapacityOneRun rank input where
  overloaded := runOverloadedOfTotalCapacityLtCardinality
    (parityCapacityOne P Item rank) input (by
      rw [totalCapacity_parityCapacityOne]
      omega)

end StructuralExhaustion.CT9
