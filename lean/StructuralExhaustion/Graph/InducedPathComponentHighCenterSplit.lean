import StructuralExhaustion.Graph.InducedPathComponentD4D7Evaluation
import StructuralExhaustion.Graph.NegativeSupportHandoff
import StructuralExhaustion.Graph.TypeBFanCenterCoordinate

namespace StructuralExhaustion.Graph.InducedPathComponentHighCenterSplit

open StructuralExhaustion

universe u

/-!
# Exact active-support high-center split

This module scans only the literal active support of one retained component.
A degree-at-least-four vertex supplies the first D6 fan-center profile.  If no
such vertex exists, a minimum-degree-three ambient baseline forces every
active-support vertex to have ambient degree exactly three.
-/

variable {V : Type u} (object : FiniteObject V)
variable (componentInput : InducedPathComponentBoundarySchedule.Input object)

noncomputable def activeHighCenters : Finset V :=
  NegativeSupportHandoff.highCentersAtLeast object 4
    (InducedPathComponentD4.activeSupport componentInput)

/-- A genuine high center found inside the identical component support. -/
structure High where
  center : V
  centerMem : center ∈ InducedPathComponentD4.activeSupport componentInput
  centerHigh : 4 ≤ object.degree center
  d6Profile : TypeBFanCenterCoordinate.Profile object
  d6ProfileExact : d6Profile = { center := center, centerHigh := centerHigh }

/-- The exact facts available after the local high-center scan fails.  The
two remaining manuscript inputs are named explicitly; neither is asserted. -/
structure NoHigh (minimumDegreeThree : 3 ≤ object.minDegree) where
  highCentersEmpty : activeHighCenters object componentInput = ∅
  ambientCubic : ∀ vertex ∈ InducedPathComponentD4.activeSupport componentInput,
    object.degree vertex = 3
  pathWitness :
    (InducedPathComponentBoundarySchedule.componentPath componentInput).IsPath

inductive Result (minimumDegreeThree : 3 ≤ object.minDegree) where
  | high (output : High object componentInput)
  | noHigh (output : NoHigh object componentInput minimumDegreeThree)

/-- Declared-order local split over the actual active-support vertices. -/
noncomputable def run (minimumDegreeThree : 3 ≤ object.minDegree) :
    Result object componentInput minimumDegreeThree := by
  classical
  by_cases nonempty : (activeHighCenters object componentInput).Nonempty
  · let center := nonempty.choose
    have centerMember := nonempty.choose_spec
    have filtered := Finset.mem_filter.mp centerMember
    let profile : TypeBFanCenterCoordinate.Profile object := {
      center := center
      centerHigh := filtered.2
    }
    exact .high {
      center := center
      centerMem := filtered.1
      centerHigh := filtered.2
      d6Profile := profile
      d6ProfileExact := rfl
    }
  · have empty : activeHighCenters object componentInput = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp nonempty
    apply Result.noHigh
    refine {
      highCentersEmpty := empty
      pathWitness := InducedPathComponentBoundarySchedule.componentPath_isPath
        componentInput
      ambientCubic := ?_
    }
    intro vertex member
    have lower : 3 ≤ object.degree vertex :=
      minimumDegreeThree.trans (object.minDegree_le_degree vertex)
    have notHigh : ¬4 ≤ object.degree vertex := by
      intro high
      have centerMember : vertex ∈ activeHighCenters object componentInput := by
        classical
        simp [activeHighCenters, NegativeSupportHandoff.highCentersAtLeast, member, high]
      rw [empty] at centerMember
      simp at centerMember
    omega

namespace High

variable (output : High object componentInput)

@[implicit_reducible]
def d6Coordinates : FinEnum
    (TypeBFanCenterCoordinate.Coordinate object output.d6Profile) :=
  TypeBFanCenterCoordinate.coordinates object output.d6Profile

theorem d6Coordinates_linear :
    (output.d6Coordinates object componentInput).card ≤
      object.input.vertices.card := by
  change TypeBFanCenterCoordinate.visibleChecks object output.d6Profile ≤
    object.input.vertices.card
  exact TypeBFanCenterCoordinate.visibleChecks_linear object output.d6Profile

end High

/-- One degree lookup per actual active-support vertex. -/
noncomputable def visibleChecks : Nat :=
  (InducedPathComponentD4.activeSupport componentInput).card

theorem visibleChecks_linear :
    visibleChecks object componentInput ≤ object.input.vertices.card := by
  unfold visibleChecks
  rw [← object.card_vertexFinset]
  apply Finset.card_le_card
  intro vertex _member
  exact object.mem_vertexFinset vertex

end StructuralExhaustion.Graph.InducedPathComponentHighCenterSplit
