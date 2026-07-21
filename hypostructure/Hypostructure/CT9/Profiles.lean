import Hypostructure.CT9.Theorems

/-!
# CT9 capacity-one and parity profiles

These profiles derive common pigeonhole capabilities from primitive label or
rank functions.  They do not own the active items: every run still queries the
exact item schedule from its literal predecessor.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

/-- Canonical capacity-one semantics for an arbitrary complete label family. -/
def capacityOneSpec {Previous : Type uPrevious}
    (Item : Previous -> Type uItem) (Label : Previous -> Type uLabel)
    (label : (previous : Previous) -> Item previous -> Label previous) :
    Spec Previous where
  Item := Item
  Label := Label
  label := label
  capacity := fun _previous _label => 1

/-- Two parity classes represented as `Fin 2`. -/
def parityLabel (rank : Nat) : Fin 2 :=
  ⟨rank % 2, Nat.mod_lt _ (by decide)⟩

/-- Complete deterministic schedule for the two parity classes. -/
def parityLabels : Core.Finite.CompleteEnumeration (Fin 2) :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

/-- Minimal reusable parity/capacity-one capability profile. -/
structure ParityCapacityOneProfile (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  rank : (previous : Previous) -> Item previous -> Nat
  items : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (Item previous)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (items.read previous) parityLabels.toEnumeration <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace ParityCapacityOneProfile

variable {Previous : Type uPrevious}

/-- Derived two-parity capacity-one CT9 semantics. -/
def spec (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous) :
    Spec Previous :=
  capacityOneSpec profile.Item (fun _previous => Fin 2)
    (fun previous item => parityLabel (profile.rank previous item))

/-- Derived executable capability. -/
def capability
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous) :
    Capability profile.spec where
  items := profile.items
  labels := fun _previous => parityLabels
  inputSize := profile.inputSize
  workCoefficient := profile.workCoefficient
  workDegree := profile.workDegree
  workBound := profile.workBound

end ParityCapacityOneProfile

/-- Exact-run package forced to the overloaded branch. -/
structure OverloadedRun {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal_eq : (run spec capability previous).terminal = .overloaded

namespace OverloadedRun

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}
  {capability : Capability spec} {previous : Previous}

/-- The exact reference execution certified by this package. -/
def result (_bundle : OverloadedRun spec capability previous) :
    ExecutionResult spec capability :=
  run spec capability previous

/-- Exact selected partition and first overloaded label. -/
def selected (bundle : OverloadedRun spec capability previous) :
    SelectedOverload capability previous :=
  bundle.result.selectedOverloadOfTerminalEq bundle.terminal_eq

/-- Extract two same-label items when every label has capacity one. -/
def sameLabelPairOfCapacityOne
    (bundle : OverloadedRun spec capability previous)
    (capacityOne : forall label : spec.Label previous,
      spec.capacity previous label = 1) :
    SameLabelPair capability previous bundle.selected.partition
      bundle.selected.residual.label :=
  bundle.selected.residual.sameLabelPairOfCapacityOne
    (capacityOne bundle.selected.residual.label)

theorem trace_eq (bundle : OverloadedRun spec capability previous) :
    bundle.result.traceNodes = Trace.expectedNodes .overloaded := by
  calc
    bundle.result.traceNodes =
        Trace.expectedNodes bundle.result.terminal :=
      bundle.result.trace_exact
    _ = Trace.expectedNodes .overloaded := by
      simpa [result] using congrArg Trace.expectedNodes bundle.terminal_eq

end OverloadedRun

/-- Force and package the overloaded reference branch from global excess. -/
def runOverloadedOfTotalCapacityLtCardinality
    {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (tooMany : totalCapacity capability previous <
      (capability.itemsAt previous).card) :
    OverloadedRun spec capability previous :=
  .mk (run_terminal_overloaded_of_totalCapacity_lt_cardinality
    spec capability previous tooMany)

/-- Exact-run package forced to the bounded branch. -/
structure BoundedRun {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous) where
  private mk ::
  terminal_eq : (run spec capability previous).terminal = .bounded

/-- Force and package the bounded branch from pointwise bounds. -/
def runBoundedOfBounded {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uItem, uLabel} Previous)
    (capability : Capability spec) (previous : Previous)
    (bounded : forall label : spec.Label previous,
      fibreCount capability previous label <= spec.capacity previous label) :
    BoundedRun spec capability previous :=
  .mk (run_terminal_bounded_of_bounded spec capability previous bounded)

/-- Same-parity pair generated from one exact CT9 overload. -/
structure SameParityPair {Previous : Type uPrevious}
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous)
    (previous : Previous) where
  private mk ::
  first : profile.Item previous
  second : profile.Item previous
  first_mem : first ∈ (profile.capability.itemsAt previous).values
  second_mem : second ∈ (profile.capability.itemsAt previous).values
  distinct : first ≠ second
  same_parity : profile.rank previous first % 2 =
    profile.rank previous second % 2

/-- Exact parity-capacity-one run forced by three scheduled items. -/
structure ParityCapacityOneRun {Previous : Type uPrevious}
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous)
    (previous : Previous) where
  private mk ::
  overloaded : OverloadedRun profile.spec profile.capability previous

namespace ParityCapacityOneRun

variable {Previous : Type uPrevious}
  {profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous}
  {previous : Previous}

/-- Exact CT9 execution carried by the parity package. -/
def result (bundle : ParityCapacityOneRun profile previous) :
    ExecutionResult profile.spec profile.capability :=
  bundle.overloaded.result

theorem terminal_eq (bundle : ParityCapacityOneRun profile previous) :
    bundle.result.terminal = .overloaded :=
  bundle.overloaded.terminal_eq

theorem trace_eq (bundle : ParityCapacityOneRun profile previous) :
    bundle.result.traceNodes = Trace.expectedNodes .overloaded :=
  bundle.overloaded.trace_eq

/-- Extract the selected same-parity collision. -/
def pair (bundle : ParityCapacityOneRun profile previous) :
    SameParityPair profile previous := by
  let pair := bundle.overloaded.sameLabelPairOfCapacityOne (fun _label => rfl)
  exact .mk pair.first pair.second pair.first_mem pair.second_mem
    pair.distinct (congrArg Fin.val pair.labels_eq)

end ParityCapacityOneRun

@[simp] theorem totalCapacity_parityCapacityOne
    {Previous : Type uPrevious}
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous)
    (previous : Previous) :
    totalCapacity profile.capability previous = 2 :=
  rfl

/-- Three scheduled items force two distinct items with equal rank parity. -/
def runParityCapacityOneOfThreeLeCardinality
    {Previous : Type uPrevious}
    (profile : ParityCapacityOneProfile.{uPrevious, uItem} Previous)
    (previous : Previous)
    (three : 3 <= (profile.capability.itemsAt previous).card) :
    ParityCapacityOneRun profile previous :=
  .mk (runOverloadedOfTotalCapacityLtCardinality profile.spec
    profile.capability previous (by
      rw [totalCapacity_parityCapacityOne]
      omega))

end Hypostructure.CT9
