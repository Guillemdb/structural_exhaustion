import HypostructurePDEExamples.FiniteModel

/-!
# Gauge semantics and target invariance
-/

namespace HypostructurePDEExamples.Gauge

open Hypostructure
open Hypostructure.PDE
open HypostructurePDEExamples.FiniteModel

def Equivalent (first second : Field) : Prop :=
  Exists fun constant : Int => forall index, second index = first index + constant

def semantics : RepresentationSemantics problem where
  equivalent := Equivalent
  equivalence := {
    refl := fun field => by
      refine Exists.intro 0 ?_
      simp
    symm := by
      intro first second equivalent
      cases equivalent with
      | intro constant shifted =>
          refine Exists.intro (-constant) ?_
          intro index
          rw [shifted index]
          simp
    trans := by
      intro first second third firstSecond secondThird
      cases firstSecond with
      | intro firstShift hFirst =>
          cases secondThird with
          | intro secondShift hSecond =>
              refine Exists.intro (firstShift + secondShift) ?_
              intro index
              rw [hSecond index, hFirst index]
              simp [add_assoc]
  }
  baseline_iff := fun _ => iff_of_true trivial trivial

def target (field : Field) : Prop := field 0 = field 1

def targetInvariant : TargetInvariant semantics target where
  target_iff := by
    intro first second equivalent
    cases equivalent with
    | intro constant shifted =>
        constructor
        · intro firstTarget
          change second 0 = second 1
          rw [shifted 0, shifted 1, firstTarget]
        · intro secondTarget
          change second 0 = second 1 at secondTarget
          rw [shifted 0, shifted 1] at secondTarget
          exact add_right_cancel secondTarget

def shift (constant : Int) (field : Field) : Field :=
  fun index => field index + constant

def gauge : GaugeInterface model semantics where
  Gauge := Int
  coordinate := fun constant _ => {
    transform := shift constant
    transformEquation := fun _ => ()
    preservesEquation := fun _ _ => trivial
    realize := shift constant
    realizes := fun _ => rfl
    preservesBaseline := fun _ => trivial
  }
  equivalent_realize := by
    intro constant window field
    refine Exists.intro (-constant) ?_
    intro index
    simp [shift]

theorem shifted_equivalent (constant : Int) (field : Field) :
    semantics.equivalent (shift constant field) field :=
  gauge.equivalent_realize constant () field

theorem target_iff_shifted (constant : Int) (field : Field) :
    target (shift constant field) <-> target field :=
  targetInvariant.target_iff (shifted_equivalent constant field)

theorem target_transports (constant : Int) (field : Field)
    (holds : target field) : target (shift constant field) :=
  (target_iff_shifted constant field).mpr holds

#print axioms shifted_equivalent
#print axioms target_iff_shifted
#print axioms target_transports

end HypostructurePDEExamples.Gauge
