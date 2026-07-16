import StructuralExhaustion.Graph.EdgeRootedReturn
import StructuralExhaustion.Graph.FiniteObject
import StructuralExhaustion.Graph.RootIncidence

namespace StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence

open StructuralExhaustion
open scoped Sym2

universe u

variable {V : Type u} {object : FiniteObject V}
variable {dart : object.graph.Dart}

/-!
# The third incidence at the root of a deleted-edge return

The input is one proof-carrying return after deleting a fixed dart.  At the
return root `dart.snd`, the first step of the return and the restored dart give
two distinct actual incidences.  `RootIncidence.classify` selects the first
declared-order third incidence.  The only subsequent test is membership of
that one endpoint in the supplied return support.

This module does not classify all support vertices and does not construct a
replacement, response vector, density statement, or target certificate.
-/

/-- Exact local input.  The degree hypotheses concern only the root of the
supplied return. -/
structure Setup (object : FiniteObject V) (dart : object.graph.Dart) where
  returnPath : DartReturn object.graph dart
  degree_ge_three : 3 ≤ object.degree dart.snd
  root_not_high : ¬3 < object.degree dart.snd

namespace Setup

/-- The deleted-edge return is nonempty because its endpoints are the two
distinct endpoints of an actual dart. -/
theorem return_not_nil (setup : Setup object dart) :
    ¬setup.returnPath.path.Nil := by
  intro isNil
  have equal : dart.snd = dart.fst := isNil.eq
  exact dart.adj.ne equal.symm

/-- The proof-carrying first step of the supplied return. -/
def firstNext (setup : Setup object dart) : V :=
  setup.returnPath.path.snd

theorem firstNext_adjacent_deleted (setup : Setup object dart) :
    (object.graph.deleteEdges {dart.edge}).Adj dart.snd setup.firstNext := by
  exact setup.returnPath.path.adj_snd setup.return_not_nil

theorem firstNext_adjacent (setup : Setup object dart) :
    object.graph.Adj dart.snd setup.firstNext :=
  object.graph.deleteEdges_le {dart.edge} setup.firstNext_adjacent_deleted

/-- The first return step cannot be the deleted root edge. -/
theorem firstNext_ne_dart_fst (setup : Setup object dart) :
    setup.firstNext ≠ dart.fst := by
  intro equal
  have adjacent := setup.firstNext_adjacent_deleted
  rw [equal] at adjacent
  simp [SimpleGraph.Dart.edge, Sym2.eq_swap] at adjacent

/-- The two literal cycle directions at the return root. -/
def divergence (setup : Setup object dart) :
    RootIncidence.Divergence object dart.snd where
  leftNext := setup.firstNext
  rightNext := dart.fst
  leftAdjacent := setup.firstNext_adjacent
  rightAdjacent := dart.adj.symm
  distinct := setup.firstNext_ne_dart_fst

/-- The root is exactly cubic; this is a local consequence of the two input
degree inequalities. -/
theorem degree_eq_three (setup : Setup object dart) :
    object.degree dart.snd = 3 := by
  have lower := setup.degree_ge_three
  have upper := Nat.le_of_not_gt setup.root_not_high
  omega

/-- The unique declared-order third incidence returned by the reusable root
classifier.  The high branch is impossible from `root_not_high`. -/
def third (setup : Setup object dart) :
    RootIncidence.Third object dart.snd setup.divergence :=
  match RootIncidence.classify object dart.snd setup.degree_ge_three
      setup.divergence with
  | .cubic _ incidence => incidence
  | .high high _ => (setup.root_not_high high).elim

theorem third_adjacent (setup : Setup object dart) :
    object.graph.Adj dart.snd setup.third.hit.value :=
  RootIncidence.Third.adjacent object dart.snd setup.third

theorem third_ne_firstNext (setup : Setup object dart) :
    setup.third.hit.value ≠ setup.firstNext :=
  RootIncidence.Third.ne_left object dart.snd setup.third

theorem third_ne_dart_fst (setup : Setup object dart) :
    setup.third.hit.value ≠ dart.fst :=
  RootIncidence.Third.ne_right object dart.snd setup.third

end Setup

/-- Exact exhaustive local classification of the selected third incidence. -/
inductive Result (setup : Setup object dart) where
  | nonRootChord
      (member : setup.third.hit.value ∈ setup.returnPath.path.support)
  | outsideBoundary
      (outside : setup.third.hit.value ∉ setup.returnPath.path.support)

/-- Run one declared-neighbour scan and one membership test in the supplied
return support. -/
def run (setup : Setup object dart) : Result setup := by
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases member : setup.third.hit.value ∈ setup.returnPath.path.support
  · exact .nonRootChord member
  · exact .outsideBoundary member

theorem run_exhaustive (setup : Setup object dart) :
    (∃ member, run setup = .nonRootChord member) ∨
    (∃ outside, run setup = .outsideBoundary outside) := by
  cases equation : run setup with
  | nonRootChord member => exact Or.inl ⟨member, rfl⟩
  | outsideBoundary outside => exact Or.inr ⟨outside, rfl⟩

/-- Conservative visible work ledger: the declared-neighbour scan, one
ambient-size allowance for checking the proof-carrying return, three constant
root checks, and the literal support-membership scan. -/
def visibleChecks (setup : Setup object dart) : Nat :=
  RootIncidence.checks object dart.snd + object.input.vertices.card + 3 +
    setup.returnPath.path.support.length

theorem visibleChecks_le (setup : Setup object dart) {scale : Nat}
    (bounded : setup.returnPath.path.support.length ≤ scale) :
    visibleChecks setup ≤ 2 * object.input.vertices.card + 3 + scale := by
  have rootChecks := RootIncidence.checks_le_order object dart.snd
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence
