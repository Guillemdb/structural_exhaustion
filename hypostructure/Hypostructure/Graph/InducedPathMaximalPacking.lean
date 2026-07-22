import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.MaximalSelection
import Hypostructure.Graph.InducedPath

/-!
# Abstract maximal induced-path packing contracts

The graph layer exposes maximal packing data without fixing a theorem-specific
path length.  A consumer supplies a residual-owned selected list and the graph
semantics needed to prove disjointness/saturation; the framework interface
publishes only maximal-packing consequences and work accounting.
-/

namespace Hypostructure.Graph.InducedPathMaximalPacking

universe u

/-- A selected induced path occurrence in an arbitrary finite graph. -/
abbrev Window (object : FiniteObject.{u}) (order : Nat) :=
  SimpleGraph.pathGraph order ↪g object.graph

noncomputable def windowSchedule (object : FiniteObject.{u}) (order : Nat) :
    Core.Finite.Enumeration (Window object order) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : FinEnum (Fin order) := inferInstance
  letI : FinEnum (Fin order → object.Vertex) := inferInstance
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : FinEnum (Window object order) :=
    FinEnum.ofInjective (fun window : Window object order =>
      (window : Fin order → object.Vertex)) (by
        intro left right equal
        exact DFunLike.coe_injective equal)
  exact Core.Finite.Enumeration.ofFinEnum inferInstance


/-- Support of one induced-path occurrence. -/
def support (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (Finset.univ : Finset (Fin order)).image window

def admissibleWindows (object : FiniteObject.{u}) (order : Nat)
    (windows : Finset (Window object order)) : Prop :=
  ∀ ⦃left right : Window object order⦄,
    left ∈ windows → right ∈ windows → left ≠ right →
      Disjoint (support object order left) (support object order right)

noncomputable def admissibleWindowSets (object : FiniteObject.{u}) (order : Nat) :
    Finset (Finset (Window object order)) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact (windowSchedule object order).toFinset.powerset.filter
    (admissibleWindows object order)

theorem admissibleWindowSets_nonempty (object : FiniteObject.{u}) (order : Nat) :
    (admissibleWindowSets object order).Nonempty := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  refine ⟨∅, ?_⟩
  simp [admissibleWindowSets, admissibleWindows]

noncomputable def maximalWindowSelection (object : FiniteObject.{u}) (order : Nat) :
    @Core.Finite.MaximalSelection.Choice (Finset (Window object order))
      (Classical.decEq _) inferInstance inferInstance
      (admissibleWindowSets object order)
      (admissibleWindowSets_nonempty object order) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact Core.Finite.MaximalSelection.chooseSelection
    (admissibleWindowSets object order)
    (admissibleWindowSets_nonempty object order)

noncomputable def maximalWindowSet (object : FiniteObject.{u}) (order : Nat) :
    Finset (Window object order) := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).value

theorem maximalWindowSet_mem (object : FiniteObject.{u}) (order : Nat) :
    maximalWindowSet object order ∈ admissibleWindowSets object order := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).mem

theorem maximalWindowSet_admissible (object : FiniteObject.{u}) (order : Nat) :
    admissibleWindows object order (maximalWindowSet object order) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact (Finset.mem_filter.mp (maximalWindowSet_mem object order)).2

theorem maximalWindowSet_maximal (object : FiniteObject.{u}) (order : Nat) :
    Maximal (fun windows => windows ∈ admissibleWindowSets object order)
      (maximalWindowSet object order) := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).maximal

theorem maximalWindowSet_saturated (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) :
    ∃ selected ∈ maximalWindowSet object order,
      ¬ Disjoint (support object order window)
        (support object order selected) ∨
      window = selected := by
  classical
  by_cases member : window ∈ maximalWindowSet object order
  · exact ⟨window, member, Or.inr rfl⟩
  · by_contra absent
    push_neg at absent
    have inserted :
        insert window (maximalWindowSet object order) ∈
          admissibleWindowSets object order := by
      have admissible := maximalWindowSet_admissible object order
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powerset.mpr
        intro item itemMem
        simp only [Finset.mem_insert] at itemMem
        rcases itemMem with rfl | itemMem
        · simp [windowSchedule]
        · have baseSubset := Finset.mem_powerset.mp
            ((Finset.mem_filter.mp (maximalWindowSet_mem object order)).1)
          exact baseSubset itemMem
      · intro left right leftMem rightMem different
        simp only [Finset.mem_insert] at leftMem rightMem
        by_cases leftNew : left = window
        · subst left
          rcases rightMem with rfl | rightMem
          · exact (different rfl).elim
          · exact (absent right rightMem).1
        · by_cases rightNew : right = window
          · subst right
            rcases leftMem with rfl | leftMem
            · exact (different rfl).elim
            · exact (absent left leftMem).1.symm
          · rcases leftMem with rfl | leftMem <;>
              rcases rightMem with rfl | rightMem
            · exact (leftNew rfl).elim
            · exact (leftNew rfl).elim
            · exact (rightNew rfl).elim
            · exact admissible leftMem rightMem different
    have maximal := maximalWindowSet_maximal object order
    have subset := maximal.2 inserted (Finset.subset_insert _ _)
    exact member (subset (Finset.mem_insert_self window _))


/-- Reusable maximal-only packing profile. -/
structure Profile (object : FiniteObject.{u}) (order : Nat) where
  selected : List (Window object order)
  selected_nodup : selected.Nodup
  pairwiseDisjoint :
    forall left, left ∈ selected -> forall right, right ∈ selected ->
      left ≠ right ->
        Disjoint (support object order left) (support object order right)
  saturated :
    forall window : Window object order,
      ∃ selectedWindow ∈ selected,
        ¬ Disjoint (support object order window)
          (support object order selectedWindow) ∨
          window = selectedWindow


def conflict (object : FiniteObject.{u}) (order : Nat)
    (left right : Window object order) : Prop :=
  ¬ Disjoint (support object order left) (support object order right)

noncomputable def Profile.toCore (profile : Profile object order) :
    @Core.Finite.MaximalSelection.Profile _
      (@Core.Finite.Enumeration.ofNodupList _ (Classical.decEq _)
        profile.selected profile.selected_nodup)
      (conflict object order) (Classical.decRel _) := by
  letI : DecidableRel (conflict object order) := Classical.decRel _
  exact {
    selected := profile.selected
    selected_nodup := profile.selected_nodup
    pairwiseCompatible := by
      intro left right leftMem rightMem different
      intro conflict
      exact conflict (profile.pairwiseDisjoint left leftMem right rightMem different)
    maximal := by
      intro item itemMem
      rcases profile.saturated item with ⟨selectedItem, selectedMem, conflictItem⟩
      exact ⟨selectedItem, selectedMem, conflictItem⟩ }

namespace Profile

variable {object : FiniteObject.{u}} {order : Nat}
variable (profile : Profile object order)

def packingNumber : Nat :=
  profile.selected.length

def workBudget : _root_.Hypostructure.Core.PolynomialCheckBudget Unit :=
  _root_.Hypostructure.Core.PolynomialCheckBudget.constant
    (fun _ => profile.packingNumber) profile.packingNumber

structure VerifiedStage : Type u where
  selected : List (Window object order)
  selected_eq : selected = profile.selected
  saturated : forall window : Window object order,
    ∃ selectedWindow ∈ profile.selected,
      ¬ Disjoint (support object order window)
        (support object order selectedWindow) ∨
      window = selectedWindow
  pairwiseDisjoint :
    forall left, left ∈ profile.selected -> forall right, right ∈ profile.selected ->
      left ≠ right ->
        Disjoint (support object order left) (support object order right)
  work : profile.workBudget.checks () = profile.packingNumber

def verifiedStage : profile.VerifiedStage where
  selected := profile.selected
  selected_eq := rfl
  saturated := profile.saturated
  pairwiseDisjoint := profile.pairwiseDisjoint
  work := rfl

/-- Framework-owned counted execution of a certified maximal packing.  The
selected family remains a primitive of the graph contract; Core owns the
ledger-facing stage and the work accounting. -/
def execute (profile : Profile object order) : profile.VerifiedStage :=
  profile.verifiedStage

@[simp] theorem execute_selected (profile : Profile object order) :
    (profile.execute).selected = profile.selected := rfl

@[simp] theorem execute_checks (profile : Profile object order) :
    profile.workBudget.checks () = profile.packingNumber := rfl

theorem nonempty_of_realization (realization : Window object order)
    (_positive : 0 < order) :
    profile.selected ≠ [] := by
  intro empty
  rcases profile.saturated realization with ⟨selectedWindow, member, _⟩
  simp [empty] at member

end Profile

end Hypostructure.Graph.InducedPathMaximalPacking
