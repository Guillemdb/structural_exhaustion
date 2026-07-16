import MantelExample.Concrete
import StructuralExhaustion.Core.FiniteJointCapacity

namespace MantelExample.FiniteJointCapacity

open StructuralExhaustion

/-!
# Joint capacity on the actual triangle-free `C₅`

The left schedule is the five vertices of the concrete Mantel graph and the
right schedule is its two local incidence orientations.  Their joint code is
the corresponding labelled vertex/orientation slot.  On `C₅` these ten slots
have exactly the cardinality of the graph's actual dart enumeration.  This
exercises the reusable joint-capacity theorem on the named graph object,
without constructing a product schedule.
-/

/-- The two local incidence orientations at each actual `C₅` vertex. -/
def orientations : Core.OrderedCollection (Fin 2) :=
  (inferInstance : FinEnum (Fin 2)).toOrderedCollection

/-- The joint encoder records the actual `C₅` vertex and its local incidence
orientation. -/
def profile : Core.FiniteJointCapacity.Profile where
  Left := ConcreteC5.Vertex
  Right := Fin 2
  Code := ConcreteC5.Vertex × Fin 2
  left := ConcreteC5.object.input.vertices.toOrderedCollection
  right := orientations
  codes := inferInstance
  encode := fun vertex orientation => (vertex, orientation)
  encodeInjectiveOnSchedules := by
    intro left₁ left₂ right₁ right₂ _ _ _ _ equal
    exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩

/-- The actual ten vertex/orientation slots fit in the ten labelled codes. -/
theorem jointCapacity_exact :
    profile.left.values.length * profile.right.values.length ≤
      profile.codes.card :=
  profile.left_mul_right_le_codeCard

/-- All three cardinalities are the literal ones of the supplied `C₅` data. -/
theorem cardinalities_exact :
    profile.left.values.length = 5 ∧
      profile.right.values.length = 2 ∧ profile.codes.card = 10 := by
  native_decide

/-- On the actual degree-two cycle, the joint code capacity is exactly the
number of oriented edges used by the Mantel dart ledger. -/
theorem codeCard_eq_actualDarts :
    profile.codes.card = ConcreteC5.object.input.darts.card := by
  native_decide

/-- The shared theorem performs no semantic pair checks. -/
theorem checks_exact : profile.checks = 0 := profile.checks_eq_zero

/-- The transfer is tied to the same actual graph object used by the Mantel
proof, not to a synthetic finite carrier. -/
theorem source_triangleFree : ConcreteC5.object.graph.CliqueFree 3 :=
  ConcreteC5.triangleFree

/-- The same concrete object satisfies Mantel's bound. -/
theorem source_mantel_bound : Target ConcreteC5.object :=
  ConcreteC5.mantel_bound

end MantelExample.FiniteJointCapacity
