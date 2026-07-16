import Mathlib.Tactic

namespace StructuralExhaustion.Core.RootedPathRelation

universe u

/-!
# Deterministic relation of two finite rooted paths

The comparison consumes two already supplied vertex words after a common
root.  It never searches for a path.  Equal next vertices extend the common
prefix; the first unequal pair exposes the last common vertex as separator;
and exhaustion of either word is the parallel (prefix, including equality)
case.
-/

variable {Vertex : Type u}

inductive Comparison (Vertex : Type u) where
  | parallel
  | separator (vertex leftNext rightNext : Vertex)
      (distinct : leftNext ≠ rightNext)

/-- Compare two path tails whose last common vertex is `root`. -/
def compare [DecidableEq Vertex] (root : Vertex) :
    List Vertex → List Vertex → Comparison Vertex
  | [], _ => .parallel
  | _, [] => .parallel
  | left :: leftTail, right :: rightTail =>
      if equal : left = right then compare left leftTail rightTail
      else .separator root left right equal

/-- One primitive equality check for each common-prefix extension, and one
final check unless one tail is exhausted. -/
def checks [DecidableEq Vertex] : List Vertex → List Vertex → Nat
  | [], _ => 0
  | _, [] => 0
  | left :: leftTail, right :: rightTail =>
      if left = right then checks leftTail rightTail + 1 else 1

theorem checks_le_left_length [DecidableEq Vertex]
    (left right : List Vertex) : checks left right ≤ left.length := by
  induction left generalizing right with
  | nil => simp [checks]
  | cons head tail ih =>
      cases right with
      | nil => simp [checks]
      | cons other rest =>
          simp only [checks, List.length_cons]
          split
          · exact Nat.succ_le_succ (ih rest)
          · omega

theorem checks_le_right_length [DecidableEq Vertex]
    (left right : List Vertex) : checks left right ≤ right.length := by
  induction left generalizing right with
  | nil => simp [checks]
  | cons head tail ih =>
      cases right with
      | nil => simp [checks]
      | cons other rest =>
          simp only [checks, List.length_cons]
          split
          · exact Nat.succ_le_succ (ih rest)
          · omega

/-- The exact recursive semantics of the returned relation. -/
def Valid [DecidableEq Vertex] (root : Vertex) :
    List Vertex → List Vertex → Comparison Vertex → Prop
  | [], _, result => result = .parallel
  | _, [], result => result = .parallel
  | left :: leftTail, right :: rightTail, result =>
      if left = right then Valid left leftTail rightTail result
      else ∃ distinct : left ≠ right,
        result = .separator root left right distinct

theorem compare_valid [DecidableEq Vertex] (root : Vertex) :
    ∀ (left right : List Vertex),
      Valid root left right (compare root left right) := by
  intro left
  induction left generalizing root with
  | nil =>
      intro right
      rfl
  | cons left leftTail ih =>
      intro right
      cases right with
      | nil => rfl
      | cons right rightTail =>
          simp only [compare, Valid]
          by_cases equal : left = right
          · simpa [equal] using ih left rightTail
          · simp [equal]

/-- Degree refinement used after the purely path-theoretic comparison. -/
inductive Routed (degree : Vertex → Nat) where
  | parallel
  | cubicSeparator (vertex leftNext rightNext : Vertex)
      (distinct : leftNext ≠ rightNext) (cubic : degree vertex = 3)
  | highSeparator (vertex leftNext rightNext : Vertex)
      (distinct : leftNext ≠ rightNext) (high : 4 ≤ degree vertex)

/-- Refine an actual separator using a supplied minimum-degree-three fact.
This is ordinary theorem composition, not a residual route. -/
def route (degree : Vertex → Nat) (minimumThree : ∀ vertex, 3 ≤ degree vertex) :
    Comparison Vertex → Routed degree
  | .parallel => .parallel
  | .separator vertex leftNext rightNext distinct =>
      if cubic : degree vertex = 3 then
        .cubicSeparator vertex leftNext rightNext distinct cubic
      else .highSeparator vertex leftNext rightNext distinct (by
        have lower := minimumThree vertex
        omega)

theorem route_exhaustive (degree : Vertex → Nat)
    (minimumThree : ∀ vertex, 3 ≤ degree vertex)
    (comparison : Comparison Vertex) :
    (∃ routed : Routed degree, routed = route degree minimumThree comparison) :=
  ⟨route degree minimumThree comparison, rfl⟩

end StructuralExhaustion.Core.RootedPathRelation
