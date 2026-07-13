import StructuralExhaustion.CT9.State

namespace StructuralExhaustion.CT9

universe uAmbient uBranch uItem uLabel

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uItem, uLabel} P)
variable (input : Input capability)

/-- The label partition is exact: every active item belongs to the fibre named
by its computed label. -/
theorem mem_own_fibre (item : capability.Item) (member : item ∈ input.items.values) :
    item ∈ fibre capability input (capability.label item) := by
  simp [fibre, member]

/-- Distinct label fibres are disjoint. -/
theorem fibre_disjoint {left right : capability.Label} (different : left ≠ right) :
    ∀ item, item ∈ fibre capability input left →
      item ∈ fibre capability input right → False := by
  intro item inLeft inRight
  simp [fibre] at inLeft inRight
  exact different (inLeft.2.symm.trans inRight.2)

/-- Exact fibres inherit duplicate-freedom from the active item collection. -/
theorem fibre_nodup (label : capability.Label) :
    (fibre capability input label).Nodup :=
  List.filter_sublist.nodup input.items.nodup

namespace OverloadResidual

/-- A capacity-one overload constructively contains two distinct active items
with the overloaded label. -/
def sameLabelPairOfCapacityOne
    {C : Capability.{uAmbient, uBranch, uItem, uLabel} P}
    {source : Input C} (residual : OverloadResidual C source)
    (capacityOne : C.capacity residual.label = 1) :
    SameLabelPair C source residual.label := by
  have moreThanOne : 1 < (fibre C source residual.label).length := by
    simpa [fibreCount, capacityOne] using residual.overloaded
  have noDuplicates := fibre_nodup C source residual.label
  cases fibres : fibre C source residual.label with
  | nil => simp [fibres] at moreThanOne
  | cons first rest =>
      cases rest with
      | nil => simp [fibres] at moreThanOne
      | cons second tail =>
          have firstInFibre :
              first ∈ fibre C source residual.label := by
            simp [fibres]
          have secondInFibre :
              second ∈ fibre C source residual.label := by
            simp [fibres]
          have firstInfo : first ∈ source.items.values ∧
              C.label first = residual.label := by
            simpa [fibre] using firstInFibre
          have secondInfo : second ∈ source.items.values ∧
              C.label second = residual.label := by
            simpa [fibre] using secondInFibre
          have listedNodup : (first :: second :: tail).Nodup := by
            simpa [fibres] using noDuplicates
          have different : first ≠ second := by
            intro equal
            exact (List.nodup_cons.mp listedNodup).1 (by simp [equal])
          exact {
            first := first
            second := second
            first_mem := firstInfo.1
            second_mem := secondInfo.1
            distinct := different
            first_label := firstInfo.2
            second_label := secondInfo.2
          }

end OverloadResidual

private theorem covered_cardinality_le_capacity
    {Item : Type uItem} {Label : Type uLabel} [DecidableEq Label]
    (itemLabel : Item → Label) (capacity : Label → Nat)
    (labels : List Label) (items : List Item)
    (covered : ∀ item, item ∈ items → itemLabel item ∈ labels)
    (bounded : ∀ label, label ∈ labels →
      (items.filter fun item => itemLabel item = label).length ≤ capacity label) :
    items.length ≤ (labels.map capacity).sum := by
  induction labels generalizing items with
  | nil =>
      cases items with
      | nil => simp
      | cons item tail =>
          have impossible : False := by
            simpa using covered item (by simp)
          exact impossible.elim
  | cons current remaining inductionHypothesis =>
      let restItems := items.filter fun item => itemLabel item ≠ current
      have restCovered : ∀ item, item ∈ restItems →
          itemLabel item ∈ remaining := by
        intro item member
        have info : item ∈ items ∧ itemLabel item ≠ current := by
          simpa [restItems] using member
        have inLabels := covered item info.1
        simp only [List.mem_cons] at inLabels
        cases inLabels with
        | inl equal => exact (info.2 equal).elim
        | inr inRemaining => exact inRemaining
      have restBounded : ∀ label, label ∈ remaining →
          (restItems.filter fun item => itemLabel item = label).length ≤
            capacity label := by
        intro label member
        have restSublist : List.Sublist restItems items := by
          exact List.filter_sublist
        have fibreSublist :=
          restSublist.filter (fun item => itemLabel item = label)
        have sublistBound := fibreSublist.length_le
        have capacityBound :=
          bounded label (List.mem_cons_of_mem current member)
        omega
      have restCardinality :
          restItems.length ≤ (remaining.map capacity).sum :=
        inductionHypothesis restItems restCovered restBounded
      have currentBound :
          (items.filter fun item => itemLabel item = current).length ≤
            capacity current :=
        bounded current (by simp)
      have partitionLength (values : List Item) :
          values.length =
            (values.filter fun item => itemLabel item = current).length +
            (values.filter fun item => itemLabel item ≠ current).length := by
        simpa [List.countP_eq_length_filter] using
          (List.length_eq_countP_add_countP
            (fun item => itemLabel item = current) (l := values))
      have split := partitionLength items
      simp only [List.map_cons, List.sum_cons]
      simp only [restItems] at restCardinality
      omega

namespace BoundedCertificate

/-- Exact label fibres partition the active collection, so pointwise capacity
bounds imply the global item-count bound. -/
theorem cardinality_le_totalCapacity
    {C : Capability.{uAmbient, uBranch, uItem, uLabel} P}
    {source : Input C} (certificate : BoundedCertificate C source) :
    source.items.values.length ≤ totalCapacity C := by
  letI : DecidableEq C.Label := C.labels.decEq
  simpa [totalCapacity] using
    (covered_cardinality_le_capacity C.label C.capacity
      C.labels.orderedValues source.items.values
      (fun item _member => C.labels.mem_orderedValues (C.label item))
      (fun label _member => by
        simpa [fibreCount, fibre] using certificate.bounded label))

/-- A collection larger than the total declared capacity cannot satisfy a
bounded certificate. -/
theorem false_of_totalCapacity_lt_cardinality
    {C : Capability.{uAmbient, uBranch, uItem, uLabel} P}
    {source : Input C} (certificate : BoundedCertificate C source)
    (tooMany : totalCapacity C < source.items.values.length) : False :=
  (Nat.not_lt_of_ge certificate.cardinality_le_totalCapacity) tooMany

end BoundedCertificate

inductive Decision where
  | overloaded (residual : OverloadResidual capability input)
  | bounded (certificate : BoundedCertificate capability input)

/-- Search labels in their declared order for the first overloaded fibre. -/
def analyze : Decision capability input :=
  match Core.FiniteSearch.search capability.labels
      (fun label => capability.capacity label < fibreCount capability input label)
      (fun _ => inferInstance) with
  | .found label overloaded => .overloaded ⟨label, overloaded⟩
  | .absent noOverload => .bounded ⟨fun label =>
      Nat.le_of_not_gt (noOverload label)⟩

/-- Materialize the first overloaded label when global cardinality exceeds
the sum of all declared capacities. -/
def overloadOfTotalCapacityLtCardinality
    (tooMany : totalCapacity capability < input.items.values.length) :
    OverloadResidual capability input :=
  match analyze capability input with
  | .overloaded residual => residual
  | .bounded certificate =>
      (certificate.false_of_totalCapacity_lt_cardinality tooMany).elim

theorem analyze_sound :
    match analyze capability input with
    | .overloaded residual =>
        capability.capacity residual.label <
          fibreCount capability input residual.label
    | .bounded _ => ∀ label,
        fibreCount capability input label ≤ capability.capacity label := by
  cases analyze capability input with
  | overloaded residual => exact residual.overloaded
  | bounded certificate => exact certificate.bounded

end StructuralExhaustion.CT9
