import StructuralExhaustion.Graph.DeletedEdgeReturnBoundaryStar
import StructuralExhaustion.Graph.DeletedEdgeReturnChordResolution

namespace StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary

open StructuralExhaustion

universe u

variable {V : Type u} {object : FiniteObject V}
variable {dart : object.graph.Dart}

/-!
# Normalizing the two local deleted-return boundary branches

This module rejoins exactly two proof-carrying local outcomes.  A rejected
on-return chord supplies its strictly shorter return; the old first return
step is then the outside incidence of that shorter return.  An already
outside third incidence retains the original return.  In either case the
same certified cubic star owns every incidence at the return root.

The construction performs no scan.  It does not construct a cold-skeleton
boundary stub, outside-vertex collection, component, successor, response
coordinate, compression input, density statement, or iteration theorem.
-/

/-- Exact rejected result of the chord resolver, retaining its complete
computed predecessor chain. -/
structure RejectedChordRun
    (setup : DeletedEdgeReturnThirdIncidence.Setup object dart)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) where
  input : DeletedEdgeReturnChordResolution.Input setup
  lengthRejected : ¬LengthOK (input.index + 1)
  shorter : DartReturn object.graph dart
  shorterExact : shorter = input.shorterReturn
  strict : shorter.path.length < setup.returnPath.path.length
  runExact : DeletedEdgeReturnChordResolution.run input LengthOK
      lengthOKDecidable =
    .rejected lengthRejected shorter shorterExact strict

namespace RejectedChordRun

variable {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}
variable {LengthOK : Nat → Prop} {lengthOKDecidable : DecidablePred LengthOK}

/-- The old first return step does not occur in the shorter return.  The
shorter suffix starts at `input.index ≥ 2`, whereas the old first step is at
position one of the original simple return. -/
theorem firstNext_not_mem_shorterReturn_support
    (branch : RejectedChordRun setup LengthOK lengthOKDecidable) :
    setup.firstNext ∉ branch.input.shorterReturn.path.support := by
  intro member
  simp only [DeletedEdgeReturnChordResolution.Input.shorterReturn,
    SimpleGraph.Walk.support_cons, List.mem_cons] at member
  rcases member with atRoot | inSuffix
  · exact setup.firstNext_adjacent.ne' atRoot
  · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at inSuffix
    obtain ⟨offset, atFirst, offsetLe⟩ := inSuffix
    have copyGet : branch.input.suffix.getVert offset =
        (setup.returnPath.path.drop branch.input.index).getVert offset := by
      simp [DeletedEdgeReturnChordResolution.Input.suffix]
    rw [copyGet, SimpleGraph.Walk.drop_getVert] at atFirst
    have sumLe : branch.input.index + offset ≤
        setup.returnPath.path.length := by
      rw [DeletedEdgeReturnChordResolution.Input.suffix,
        SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.drop_length] at offsetLe
      have indexLe := branch.input.index_le_length
      omega
    have oneLe : 1 ≤ setup.returnPath.path.length := by
      have positive : 0 < setup.returnPath.path.length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp setup.return_not_nil
      omega
    have firstAtOne : setup.returnPath.path.getVert 1 = setup.firstNext := by
      change setup.returnPath.path.getVert 1 = setup.returnPath.path.snd
      simp
    have equalIndex : branch.input.index + offset = 1 :=
      setup.returnPath.isPath.getVert_injOn sumLe oneLe
        (atFirst.trans firstAtOne.symm)
    have lower := branch.input.two_le_index
    omega

theorem firstNext_not_mem_shorter_support
    (branch : RejectedChordRun setup LengthOK lengthOKDecidable) :
    setup.firstNext ∉ branch.shorter.path.support := by
  rw [branch.shorterExact]
  exact branch.firstNext_not_mem_shorterReturn_support

end RejectedChordRun

/-- The two exact local inputs to the proof-only rejoin. -/
inductive Input
    (setup : DeletedEdgeReturnThirdIncidence.Setup object dart)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    (scale : Nat) where
  | rejectedChord
      (branch : RejectedChordRun setup LengthOK lengthOKDecidable)
      (originalBound : setup.returnPath.path.support.length ≤ scale)
  | outsideBoundary
      (branch : DeletedEdgeReturnBoundaryStar.OutsideRun setup)
      (originalBound : setup.returnPath.path.support.length ≤ scale)

namespace Input

variable {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}
variable {LengthOK : Nat → Prop} {lengthOKDecidable : DecidablePred LengthOK}
variable {scale : Nat}

/-- The normalized return: shorter on chord rejection, unchanged on the
already-outside branch. -/
noncomputable def selectedReturn
    (input : Input setup LengthOK lengthOKDecidable scale) :
    DartReturn object.graph dart :=
  match input with
  | .rejectedChord branch _ => branch.shorter
  | .outsideBoundary _ _ => setup.returnPath

/-- The selected outside endpoint.  On chord rejection this is the old first
return step; on the outside branch it is the computed third endpoint. -/
noncomputable def outsideVertex
    (input : Input setup LengthOK lengthOKDecidable scale) : V :=
  match input with
  | .rejectedChord _ _ => setup.firstNext
  | .outsideBoundary _ _ => setup.third.hit.value

/-- The cubic ownership data shared by both branches. -/
noncomputable def cubicStar
    (_input : Input setup LengthOK lengthOKDecidable scale) :
    CubicStar.Data object dart.snd :=
  CubicStar.ofRootDivergence object setup.divergence setup.third
    setup.degree_eq_three

/-- Branch-sensitive decrease evidence.  The chord branch is strict; the
outside branch retains the original return definitionally. -/
def DecreaseEvidence
    (input : Input setup LengthOK lengthOKDecidable scale) : Prop :=
  match input with
  | .rejectedChord _ _ =>
      input.selectedReturn.path.length < setup.returnPath.path.length
  | .outsideBoundary _ _ =>
      input.selectedReturn.path.length = setup.returnPath.path.length

end Input

/-- One normalized proof-carrying return boundary.  It asserts only the
literal selected support, one outside incidence, cubic ownership at its root,
and the inherited local length bound. -/
structure NormalizedReturnBoundary
    {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}
    {LengthOK : Nat → Prop} {lengthOKDecidable : DecidablePred LengthOK}
    {scale : Nat}
    (input : Input setup LengthOK lengthOKDecidable scale) where
  selectedReturn : DartReturn object.graph dart
  selectedReturn_eq : selectedReturn = input.selectedReturn
  outsideVertex : V
  outsideVertex_eq : outsideVertex = input.outsideVertex
  root_mem_support : dart.snd ∈ selectedReturn.path.support
  outside_not_mem_support : outsideVertex ∉ selectedReturn.path.support
  outside_adjacent : object.graph.Adj dart.snd outsideVertex
  cubicStar : CubicStar.Data object dart.snd
  cubicStar_eq : cubicStar = input.cubicStar
  ownsAllRootIncidences :
    ∀ vertex, object.graph.Adj dart.snd vertex →
      vertex = cubicStar.first ∨ vertex = cubicStar.second ∨
        vertex = cubicStar.third
  length_le_original :
    selectedReturn.path.length ≤ setup.returnPath.path.length
  support_bound : selectedReturn.path.support.length ≤ scale
  decreaseEvidence : input.DecreaseEvidence

/-- Rejoin the exact two inputs by proof transformation only. -/
noncomputable def normalize
    {setup : DeletedEdgeReturnThirdIncidence.Setup object dart}
    {LengthOK : Nat → Prop} {lengthOKDecidable : DecidablePred LengthOK}
    {scale : Nat}
    (input : Input setup LengthOK lengthOKDecidable scale) :
    NormalizedReturnBoundary input := by
  cases input with
  | rejectedChord branch originalBound =>
      refine {
        selectedReturn := branch.shorter
        selectedReturn_eq := rfl
        outsideVertex := setup.firstNext
        outsideVertex_eq := rfl
        root_mem_support := branch.shorter.path.start_mem_support
        outside_not_mem_support := branch.firstNext_not_mem_shorter_support
        outside_adjacent := setup.firstNext_adjacent
        cubicStar := CubicStar.ofRootDivergence object setup.divergence
          setup.third setup.degree_eq_three
        cubicStar_eq := rfl
        ownsAllRootIncidences := ?_
        length_le_original := Nat.le_of_lt branch.strict
        support_bound := ?_
        decreaseEvidence := branch.strict
      }
      · intro vertex adjacent
        let star := CubicStar.ofRootDivergence object setup.divergence
          setup.third setup.degree_eq_three
        have member := (CubicStar.Data.adjacent_iff_mem_boundary object star vertex).1
          adjacent
        letI : DecidableEq V := object.input.vertices.decEq
        simp only [CubicStar.Data.boundary, Finset.mem_insert,
          Finset.mem_singleton] at member
        exact member
      · rw [SimpleGraph.Walk.length_support] at originalBound ⊢
        have strict := branch.strict
        omega
  | outsideBoundary branch originalBound =>
      refine {
        selectedReturn := setup.returnPath
        selectedReturn_eq := rfl
        outsideVertex := setup.third.hit.value
        outsideVertex_eq := rfl
        root_mem_support := setup.returnPath.path.start_mem_support
        outside_not_mem_support := branch.outside
        outside_adjacent := setup.third_adjacent
        cubicStar := branch.cubicStar
        cubicStar_eq := rfl
        ownsAllRootIncidences := ?_
        length_le_original := Nat.le_refl _
        support_bound := originalBound
        decreaseEvidence := rfl
      }
      intro vertex adjacent
      have member :=
        (CubicStar.Data.adjacent_iff_mem_boundary object branch.cubicStar vertex).1
          adjacent
      letI : DecidableEq V := object.input.vertices.decEq
      simp only [CubicStar.Data.boundary, Finset.mem_insert,
        Finset.mem_singleton] at member
      exact member

/-- Normalization itself performs no primitive checks. -/
def additionalChecks : Nat := 0

theorem additionalChecks_eq_zero : additionalChecks = 0 := rfl

end StructuralExhaustion.Graph.DeletedEdgeReturnNormalizedBoundary
