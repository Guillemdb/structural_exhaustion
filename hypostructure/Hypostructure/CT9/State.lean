import Hypostructure.CT9.Capability
import Hypostructure.Core.Finite.Accounting

/-!
# CT9 generated partition states

Every fibre is computed from the exact predecessor-owned item schedule.  The
partition and bounded-certificate constructors are private, so applications
cannot select a label or manufacture a completed partition.
-/

namespace Hypostructure.CT9

universe uPrevious uItem uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uItem, uLabel} Previous}

/-- Exact ordered fibre of one label. -/
def fibre (capability : Capability spec) (previous : Previous)
    (label : spec.Label previous) : List (spec.Item previous) := by
  letI : DecidableEq (spec.Label previous) :=
    (capability.labelScheduleAt previous).decEq
  exact (capability.itemsAt previous).values.filter fun item =>
    spec.label previous item = label

/-- Exact cardinality of one computed fibre. -/
def fibreCount (capability : Capability spec) (previous : Previous)
    (label : spec.Label previous) : Nat :=
  (fibre capability previous label).length

/-- Total declared capacity over the complete label schedule. -/
def totalCapacity (capability : Capability spec) (previous : Previous) : Nat :=
  (capability.labelScheduleAt previous).values.map
    (spec.capacity previous) |>.sum

/-- Canonical framework-owned partition of the incoming item schedule. -/
structure Partition (capability : Capability spec) (previous : Previous) where
  private mk ::
  fibres : spec.Label previous -> List (spec.Item previous)
  fibres_exact : forall label,
    fibres label = fibre capability previous label

/-- Compute the unique exact partition. -/
def computePartition (capability : Capability spec) (previous : Previous) :
    Partition capability previous :=
  .mk (fibre capability previous) (fun _label => rfl)

namespace Partition

/-- Cardinality of one generated partition fibre. -/
def count {capability : Capability spec} {previous : Previous}
    (partition : Partition capability previous)
    (label : spec.Label previous) : Nat :=
  (partition.fibres label).length

theorem count_exact {capability : Capability spec} {previous : Previous}
    (partition : Partition capability previous)
    (label : spec.Label previous) :
    partition.count label = fibreCount capability previous label := by
  simp [count, partition.fibres_exact label, fibreCount]

/-- Every generated fibre is a duplicate-free sublist of the predecessor
schedule. -/
theorem fibres_nodup {capability : Capability spec} {previous : Previous}
    (partition : Partition capability previous)
    (label : spec.Label previous) :
    (partition.fibres label).Nodup := by
  rw [partition.fibres_exact label]
  exact List.filter_sublist.nodup (capability.itemsAt previous).nodup

end Partition

/-- One generated fibre exceeds its declared capacity. -/
def Overloaded (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous)
    (label : spec.Label previous) : Prop :=
  spec.capacity previous label < partition.count label

/-- The first overloaded label in the complete authored label order. -/
abbrev OverloadResidual (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :=
  Core.Finite.Search.IndexedHit (capability.labelScheduleAt previous)
    (Overloaded capability previous partition)

namespace OverloadResidual

/-- Canonically selected overloaded label. -/
def label {capability : Capability spec} {previous : Previous}
    {partition : Partition capability previous}
    (residual : OverloadResidual capability previous partition) :
    spec.Label previous :=
  residual.value

theorem overloaded {capability : Capability spec} {previous : Previous}
    {partition : Partition capability previous}
    (residual : OverloadResidual capability previous partition) :
    spec.capacity previous residual.label <
      partition.count residual.label :=
  residual.sound

theorem scheduled {capability : Capability spec} {previous : Previous}
    {partition : Partition capability previous}
    (residual : OverloadResidual capability previous partition) :
    residual.label ∈ (capability.labelScheduleAt previous).values :=
  residual.member

end OverloadResidual

/-- Exhaustive absence of overload in the exact label scan. -/
abbrev AvoidsOverload (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous) :=
  Core.Finite.Search.Avoids (capability.labelScheduleAt previous)
    (Overloaded capability previous partition)

/-- Complete pointwise capacity certificate for the generated partition. -/
structure BoundedCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  partition : Partition capability previous
  searchComplete : AvoidsOverload capability previous partition
  bounded : forall label : spec.Label previous,
    partition.count label <= spec.capacity previous label

/-- Convert Core's exhaustive no-hit branch into an all-label certificate,
using completeness of the authored label schedule. -/
def boundedCertificateOfAvoids (capability : Capability spec)
    (previous : Previous) (partition : Partition capability previous)
    (avoids : AvoidsOverload capability previous partition) :
    BoundedCertificate capability previous :=
  .mk partition avoids (by
    intro label
    have member := (capability.labelsAt previous).complete label
    obtain ⟨index, indexed⟩ :=
      ((capability.labelScheduleAt previous).mem_iff_exists_index label).mp
        member
    have notOverloaded := avoids index
    rw [indexed] at notOverloaded
    exact Nat.le_of_not_gt notOverloaded)

/-- Two distinct incoming items in one exact generated fibre. -/
structure SameLabelPair (capability : Capability spec) (previous : Previous)
    (partition : Partition capability previous)
    (label : spec.Label previous) where
  private mk ::
  first : spec.Item previous
  second : spec.Item previous
  first_mem : first ∈ (capability.itemsAt previous).values
  second_mem : second ∈ (capability.itemsAt previous).values
  distinct : first ≠ second
  first_label : spec.label previous first = label
  second_label : spec.label previous second = label

namespace SameLabelPair

theorem labels_eq {capability : Capability spec} {previous : Previous}
    {partition : Partition capability previous}
    {label : spec.Label previous}
    (pair : SameLabelPair capability previous partition label) :
    spec.label previous pair.first = spec.label previous pair.second :=
  pair.first_label.trans pair.second_label.symm

end SameLabelPair

namespace OverloadResidual

/-- A capacity-one overload contains two distinct scheduled items carrying
the canonically selected label. -/
def sameLabelPairOfCapacityOne
    {capability : Capability spec} {previous : Previous}
    {partition : Partition capability previous}
    (residual : OverloadResidual capability previous partition)
    (capacityOne : spec.capacity previous residual.label = 1) :
    SameLabelPair capability previous partition residual.label := by
  have moreThanOne : 1 < (partition.fibres residual.label).length := by
    simpa [Partition.count, capacityOne] using residual.overloaded
  have noDuplicates := partition.fibres_nodup residual.label
  cases fibres : partition.fibres residual.label with
  | nil => simp [fibres] at moreThanOne
  | cons first rest =>
      cases rest with
      | nil => simp [fibres] at moreThanOne
      | cons second tail =>
          have firstInFibre :
              first ∈ partition.fibres residual.label := by
            simp [fibres]
          have secondInFibre :
              second ∈ partition.fibres residual.label := by
            simp [fibres]
          have firstFiltered :
              first ∈ fibre capability previous residual.label := by
            simpa [partition.fibres_exact residual.label] using firstInFibre
          have secondFiltered :
              second ∈ fibre capability previous residual.label := by
            simpa [partition.fibres_exact residual.label] using secondInFibre
          have firstInfo :
              first ∈ (capability.itemsAt previous).values ∧
                spec.label previous first = residual.label := by
            simpa [fibre] using firstFiltered
          have secondInfo :
              second ∈ (capability.itemsAt previous).values ∧
                spec.label previous second = residual.label := by
            simpa [fibre] using secondFiltered
          have listedNodup : (first :: second :: tail).Nodup := by
            simpa [fibres] using noDuplicates
          have different : first ≠ second := by
            intro equal
            exact (List.nodup_cons.mp listedNodup).1 (by simp [equal])
          exact .mk first second firstInfo.1 secondInfo.1 different
            firstInfo.2 secondInfo.2

end OverloadResidual

end Hypostructure.CT9
