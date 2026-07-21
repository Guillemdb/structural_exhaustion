import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Assembly.Locality
import Hypostructure.Core.Coordinate.Transport

namespace Hypostructure.Fixtures.CoordinatesAndAssembly

open Hypostructure.Core

def additiveProblem : Problem where
  Ambient := Int
  Baseline := fun _ => True
  BranchState := fun _ => Unit

inductive Coordinate where
  | original
  | shifted
  | normalized

inductive Primitive : Coordinate -> Coordinate -> Type
  | shift : Primitive .original .shifted
  | normalize : Primitive .shifted .normalized

def coordinates : CoordinateSystem additiveProblem where
  Coordinate := Coordinate
  Object := fun _ => Int
  realize := fun _ value => value
  Primitive := Primitive
  act := fun step value =>
    match step with
    | .shift => value + 1
    | .normalize => value - 1

def baselineTransport : PrimitiveBaselineTransport coordinates where
  preserves := by intros; trivial

def twoStep : CoordinatePath coordinates .original .normalized :=
  .cons .shift (.cons .normalize .nil)

example (value : Int) : twoStep.run value = value := by
  simp [twoStep, coordinates]

example (value : Int) :
    additiveProblem.Baseline (coordinates.realize .normalized (twoStep.run value)) :=
  twoStep.transportBaseline baselineTransport value trivial

def additiveSemantics : SemanticEquivalence additiveProblem :=
  SemanticEquivalence.equality additiveProblem

def additiveAssembly : AtomContextAssembly additiveProblem additiveSemantics where
  Interface := Unit
  Site := fun _ => Unit
  interface := fun _ _ => ()
  Atom := fun _ => Int
  Context := fun _ => Int
  compatible := fun atom context => atom + context = atom + context
  atom := fun object _ => object
  context := fun _ _ => 0
  assemble := (· + ·)
  extractedCompatible := by intros; rfl
  reconstruct := by intros; simp [additiveSemantics, SemanticEquivalence.equality]

example (value : Int) :
    additiveAssembly.assemble
      (additiveAssembly.atom value ()) (additiveAssembly.context value ()) = value := by
  simp [additiveAssembly]

def additiveReplacement (value replacementAtom : Int) :
    additiveAssembly.Replacement value () where
  atom := replacementAtom
  compatible := rfl

example (value replacementAtom : Int) :
    additiveAssembly.replace (additiveReplacement value replacementAtom) =
      replacementAtom := by
  simp [AtomContextAssembly.replace, additiveAssembly, additiveReplacement]

end Hypostructure.Fixtures.CoordinatesAndAssembly
