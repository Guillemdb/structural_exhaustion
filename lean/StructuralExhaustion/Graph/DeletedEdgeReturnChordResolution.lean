import StructuralExhaustion.Graph.ChordCycle
import StructuralExhaustion.Graph.DeletedEdgeReturnThirdIncidence

namespace StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}
variable {dart : object.graph.Dart}

/-!
# Resolving an on-return third incidence

This module consumes the exact `nonRootChord` result of the local third-
incidence classifier.  It scans only the supplied return support for the
canonical position of that one endpoint.  The resulting chord either has an
accepted length or supplies a strictly shorter return after the same deleted
root edge.
-/

/-- Proof-carrying input from the exact generic predecessor execution. -/
structure Input (setup : DeletedEdgeReturnThirdIncidence.Setup object dart) where
  member : setup.third.hit.value ∈ setup.returnPath.path.support
  runExact : DeletedEdgeReturnThirdIncidence.run setup = .nonRootChord member

namespace Input

variable {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}

/-- Canonical position found by one scan of the supplied support. -/
def index (input : Input setup) : Nat := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact setup.returnPath.path.support.idxOf setup.third.hit.value

theorem index_lt_support (input : Input setup) :
    input.index < setup.returnPath.path.support.length := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact List.idxOf_lt_length_iff.mpr input.member

theorem support_at_index (input : Input setup) :
    setup.returnPath.path.support[input.index]'input.index_lt_support =
      setup.third.hit.value := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact List.getElem_idxOf input.index_lt_support

theorem index_le_length (input : Input setup) :
    input.index ≤ setup.returnPath.path.length := by
  have bound := input.index_lt_support
  rw [SimpleGraph.Walk.length_support] at bound
  omega

theorem getVert_index (input : Input setup) :
    setup.returnPath.path.getVert input.index = setup.third.hit.value := by
  rw [setup.returnPath.path.getVert_eq_support_getElem input.index_le_length]
  exact input.support_at_index

theorem index_ne_zero (input : Input setup) : input.index ≠ 0 := by
  intro equal
  have third_eq_root : setup.third.hit.value = dart.snd := by
    rw [← input.getVert_index, equal, SimpleGraph.Walk.getVert_zero]
  exact setup.third_adjacent.ne' third_eq_root

theorem one_lt_index (input : Input setup) : 1 < input.index := by
  have firstAtOne : setup.returnPath.path.getVert 1 = setup.firstNext := by
    change setup.returnPath.path.getVert 1 = setup.returnPath.path.snd
    simpa using setup.returnPath.path.getVert_succ 0
  have index_ne_one : input.index ≠ 1 := by
    intro equal
    apply setup.third_ne_firstNext
    rw [← input.getVert_index, equal, firstAtOne]
  have index_ne_zero := input.index_ne_zero
  omega

theorem two_le_index (input : Input setup) : 2 ≤ input.index := by
  exact input.one_lt_index

theorem index_lt_length (input : Input setup) :
    input.index < setup.returnPath.path.length := by
  have endpointAtLength :
      setup.returnPath.path.getVert setup.returnPath.path.length = dart.fst :=
    setup.returnPath.path.getVert_length
  have index_ne_length : input.index ≠ setup.returnPath.path.length := by
    intro equal
    apply setup.third_ne_dart_fst
    rw [← input.getVert_index, equal, endpointAtLength]
  exact Nat.lt_of_le_of_ne input.index_le_length index_ne_length

/-- Ambient rooted view of the identical supplied deleted-edge return. -/
noncomputable def ambientRootedPath (input : Input setup) :
    RootedPath object.graph dart.fst where
  endpoint := dart.snd
  path :=
    ⟨setup.returnPath.path.mapLe
        (object.graph.deleteEdges_le {dart.edge}),
      setup.returnPath.isPath.mapLe _⟩

theorem ambient_length (input : Input setup) :
    input.ambientRootedPath.length = setup.returnPath.path.length := by
  change (setup.returnPath.path.map _).length = setup.returnPath.path.length
  exact SimpleGraph.Walk.length_map _ _

theorem ambient_getVert (input : Input setup) (position : Nat) :
    input.ambientRootedPath.path.val.getVert position =
      setup.returnPath.path.getVert position := by
  change (setup.returnPath.path.map _).getVert position = _
  exact SimpleGraph.Walk.getVert_map _ _ _

theorem first_adjacent (input : Input setup) :
    object.graph.Adj input.ambientRootedPath.endpoint
      (input.ambientRootedPath.path.val.getVert 1) := by
  rw [input.ambient_getVert]
  change object.graph.Adj dart.snd (setup.returnPath.path.getVert 1)
  have positive : 0 < setup.returnPath.path.length := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp setup.return_not_nil
  simpa using
    object.graph.deleteEdges_le {dart.edge}
      (setup.returnPath.path.adj_getVert_succ positive)

theorem third_adjacent_at_index (input : Input setup) :
    object.graph.Adj input.ambientRootedPath.endpoint
      (input.ambientRootedPath.path.val.getVert input.index) := by
  rw [input.ambient_getVert, input.getVert_index]
  exact setup.third_adjacent

/-- Literal ambient cycle cut out by the first return edge and the selected
third incidence. -/
noncomputable def chordCycle (input : Input setup) :
    object.graph.Walk dart.snd dart.snd :=
  (input.ambientRootedPath.chordCycle 1 input.index input.one_lt_index.le
    input.first_adjacent input.third_adjacent_at_index).copy rfl rfl

theorem chordCycle_isCycle (input : Input setup) :
    input.chordCycle.IsCycle := by
  rw [chordCycle, SimpleGraph.Walk.isCycle_copy]
  exact input.ambientRootedPath.chordCycle_isCycle input.one_lt_index
    (by rw [input.ambient_length]; exact input.index_le_length)
    input.first_adjacent input.third_adjacent_at_index

theorem chordCycle_length (input : Input setup) :
    input.chordCycle.length = input.index + 1 := by
  rw [chordCycle, SimpleGraph.Walk.length_copy,
    input.ambientRootedPath.chordCycle_length input.one_lt_index
      (by rw [input.ambient_length]; exact input.index_le_length)
      input.first_adjacent input.third_adjacent_at_index]
  have lower := input.one_lt_index
  omega

theorem third_adjacent_deleted (input : Input setup) :
    (object.graph.deleteEdges {dart.edge}).Adj dart.snd
      setup.third.hit.value := by
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨setup.third_adjacent, ?_⟩
  simp only [Set.mem_singleton_iff, SimpleGraph.Dart.edge]
  intro equal
  rcases Sym2.eq_iff.mp equal with equal | equal
  · exact dart.adj.ne equal.1.symm
  · exact setup.third_ne_dart_fst equal.2

/-- The suffix beginning at the canonical third-incidence position. -/
noncomputable def suffix (input : Input setup) :
    (object.graph.deleteEdges {dart.edge}).Walk
      setup.third.hit.value dart.fst :=
  (setup.returnPath.path.drop input.index).copy input.getVert_index rfl

theorem root_not_mem_suffix (input : Input setup) :
    dart.snd ∉ input.suffix.support := by
  intro member
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at member
  obtain ⟨offset, atRoot, offsetLe⟩ := member
  have mapped : setup.returnPath.path.getVert (input.index + offset) = dart.snd := by
    have copyGet : input.suffix.getVert offset =
        (setup.returnPath.path.drop input.index).getVert offset := by
      simp [suffix]
    rw [copyGet, SimpleGraph.Walk.drop_getVert] at atRoot
    exact atRoot
  have startRoot : setup.returnPath.path.getVert 0 = dart.snd :=
    setup.returnPath.path.getVert_zero
  have sumLe : input.index + offset ≤ setup.returnPath.path.length := by
    rw [suffix, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.drop_length] at offsetLe
    have indexLe := input.index_le_length
    omega
  have equalIndex : input.index + offset = 0 :=
    setup.returnPath.isPath.getVert_injOn sumLe (by simp) (mapped.trans startRoot.symm)
  exact input.index_ne_zero (by omega)

/-- Replace the initial return prefix by the selected third edge. -/
noncomputable def shorterReturn (input : Input setup) :
    DartReturn object.graph dart where
  path := .cons input.third_adjacent_deleted input.suffix
  isPath := by
    apply SimpleGraph.Walk.IsPath.cons
    · rw [suffix, SimpleGraph.Walk.isPath_copy]
      exact setup.returnPath.isPath.drop input.index
    · exact input.root_not_mem_suffix

theorem shorterReturn_length (input : Input setup) :
    input.shorterReturn.path.length =
      setup.returnPath.path.length - input.index + 1 := by
  simp [shorterReturn, suffix]

theorem shorterReturn_strict (input : Input setup) :
    input.shorterReturn.path.length < setup.returnPath.path.length := by
  rw [input.shorterReturn_length]
  have indexLe := input.index_le_length
  have indexTwo := input.one_lt_index
  omega

end Input

/-- Exhaustive result of deciding the application-supplied target predicate
on the one locally constructed chord cycle. -/
inductive Result {setup : DeletedEdgeReturnThirdIncidence.Setup object dart} (input : Input setup)
    (LengthOK : Nat → Prop) where
  | target (certificate : CycleWithLength object.graph LengthOK)
  | rejected
      (lengthRejected : ¬LengthOK (input.index + 1))
      (shorter : DartReturn object.graph dart)
      (shorterExact : shorter = input.shorterReturn)
      (strict : shorter.path.length < setup.returnPath.path.length)

/-- One support scan followed by one target-length decision. -/
noncomputable def run {setup : DeletedEdgeReturnThirdIncidence.Setup object dart} (input : Input setup)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    Result input LengthOK :=
  match lengthOKDecidable (input.index + 1) with
  | .isTrue accepted => .target {
      vertex := dart.snd
      walk := input.chordCycle
      isCycle := input.chordCycle_isCycle
      length_ok := by simpa [input.chordCycle_length] using accepted
    }
  | .isFalse rejected =>
      .rejected rejected input.shorterReturn rfl input.shorterReturn_strict

theorem run_exhaustive {setup : DeletedEdgeReturnThirdIncidence.Setup object dart} (input : Input setup)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    (∃ certificate, run input LengthOK lengthOKDecidable = .target certificate) ∨
    (∃ rejected shorter shorterExact strict,
      run input LengthOK lengthOKDecidable =
        .rejected rejected shorter shorterExact strict) := by
  cases equation : run input LengthOK lengthOKDecidable with
  | target certificate => exact Or.inl ⟨certificate, rfl⟩
  | rejected rejected shorter shorterExact strict =>
      exact Or.inr ⟨rejected, shorter, shorterExact, strict, rfl⟩

/-- Visible local work: at most one full support scan and one length test. -/
def visibleChecks {setup : DeletedEdgeReturnThirdIncidence.Setup object dart} (_input : Input setup) : Nat :=
  setup.returnPath.path.support.length + 1

theorem visibleChecks_le {setup : DeletedEdgeReturnThirdIncidence.Setup object dart} (input : Input setup)
    {scale : Nat} (bounded : setup.returnPath.path.support.length ≤ scale) :
    visibleChecks input ≤ scale + 1 := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution
