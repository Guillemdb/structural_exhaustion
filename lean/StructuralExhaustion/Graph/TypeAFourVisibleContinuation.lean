import StructuralExhaustion.Graph.TypeADeclaredContinuationCoordinate

namespace StructuralExhaustion.Graph.TypeAFourVisibleContinuation

open StructuralExhaustion
open TypeACanonicalReceiverTrace

universe u v w x y z

variable {V : Type u} (object : FiniteObject V)
variable (profile : SupportProfile object)
variable (port : TypeAAnchoredReturnCoordinate.Port object profile)
variable (Load : Type z) (Label : Type v) (SupportDatum : Type w)
variable (Value : Type x) (Fibre : Type y)

abbrev Coordinate := TypeADeclaredContinuationCoordinate.Coordinate object
  profile port Label SupportDatum Value Fibre

/-- The actual node-[93] visible-return schedule at one fixed completion port.
Every entry is a proof-carrying declared coordinate, not a path description to
be searched for.  `unpeeled` and `visible` retain exactly the two predecessor
properties needed by the manuscript branch. -/
structure Schedule where
  Entry : Type (max u v w x y z)
  entries : List Entry
  coordinate : Entry → Coordinate object profile port Label SupportDatum Value Fibre
  load : Entry → Load
  Unpeeled : Load → Prop
  Visible : Entry → Prop
  all_unpeeled : ∀ entry ∈ entries, Unpeeled (load entry)
  all_visible : ∀ entry ∈ entries, Visible entry
  loads_nodup : (entries.map load).Nodup
  same_fibre : ∀ entry ∈ entries, ∀ other ∈ entries,
    (coordinate entry).fibreImage = (coordinate other).fibreImage

namespace Schedule

variable {Load Label SupportDatum Value Fibre}

/-- Literal first-four output.  The index is `Fin 4`, so no fifth case or
residual constructor is introduced. -/
structure Four
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre) where
  entry : Fin 4 → schedule.Entry
  entry_mem : ∀ i, entry i ∈ schedule.entries
  load_injective : Function.Injective (fun i => schedule.load (entry i))
  unpeeled : ∀ i, schedule.Unpeeled (schedule.load (entry i))
  visible : ∀ i, schedule.Visible (entry i)

/-- Node `[93]` yes-branch producer: take positions `0,1,2,3` from the one
actual stored schedule. -/
noncomputable def firstFour
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre)
    (atLeastFour : 4 ≤ schedule.entries.length) : schedule.Four := by
  let chosen : Fin 4 → schedule.Entry := fun i =>
    schedule.entries.get ⟨i.1, lt_of_lt_of_le i.2 atLeastFour⟩
  refine {
    entry := chosen
    entry_mem := ?_
    load_injective := ?_
    unpeeled := ?_
    visible := ?_ }
  · intro i
    exact List.get_mem schedule.entries
      ⟨i.1, lt_of_lt_of_le i.2 atLeastFour⟩
  · intro i j equalLoad
    apply Fin.ext
    have mappedNodup := schedule.loads_nodup
    have iBound : i.1 < schedule.entries.length := lt_of_lt_of_le i.2 atLeastFour
    have jBound : j.1 < schedule.entries.length := lt_of_lt_of_le j.2 atLeastFour
    have mappedI : (schedule.entries.map schedule.load)[i.1]'(by simpa using iBound) =
        schedule.load (chosen i) := by simp [chosen]
    have mappedJ : (schedule.entries.map schedule.load)[j.1]'(by simpa using jBound) =
        schedule.load (chosen j) := by simp [chosen]
    have iMapBound : i.1 < (schedule.entries.map schedule.load).length := by
      simpa using iBound
    have jMapBound : j.1 < (schedule.entries.map schedule.load).length := by
      simpa using jBound
    have eqMapped :
        (schedule.entries.map schedule.load)[i.1]'iMapBound =
          (schedule.entries.map schedule.load)[j.1]'jMapBound := by
      exact mappedI.trans (equalLoad.trans mappedJ.symm)
    have eqIndex : i.1 = j.1 :=
      mappedNodup.getElem_inj_iff.mp eqMapped
    exact eqIndex
  · intro i
    exact schedule.all_unpeeled _ (List.get_mem schedule.entries
      ⟨i.1, lt_of_lt_of_le i.2 atLeastFour⟩)
  · intro i
    exact schedule.all_visible _ (List.get_mem schedule.entries
      ⟨i.1, lt_of_lt_of_le i.2 atLeastFour⟩)

def coordinates
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre)
    (four : schedule.Four) : List (Coordinate object profile port Label
      SupportDatum Value Fibre) :=
  List.ofFn fun i => schedule.coordinate (four.entry i)

@[simp] theorem coordinates_length
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre)
    (four : schedule.Four) :
    (coordinates object profile port schedule four).length = 4 := by
  simp [coordinates]

/-- The selected four coordinates as the exact same-fibre input expected by
the existing continuation classifier. -/
def family
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre)
    (four : schedule.Four) :
    TypeADeclaredContinuationCoordinate.Family object profile port Label
      SupportDatum Value Fibre where
  coordinates := coordinates object profile port schedule four
  nonempty := by simp [coordinates]
  sameFibre := by
    intro coordinate member
    rw [coordinates] at member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    let lastIndex : Fin 4 := ⟨3, by omega⟩
    have lastEq : (coordinates object profile port schedule four).getLast (by
        simp [coordinates]) = schedule.coordinate (four.entry lastIndex) := by
      simp [coordinates, lastIndex]
    rw [lastEq]
    exact schedule.same_fibre _ (four.entry_mem i) _ (four.entry_mem lastIndex)

theorem family_has_four
    (schedule : Schedule object profile port Load Label SupportDatum Value Fibre)
    (four : schedule.Four) :
    (family object profile port schedule four).coordinates.length = 4 :=
  coordinates_length object profile port schedule four

end Schedule

end StructuralExhaustion.Graph.TypeAFourVisibleContinuation
