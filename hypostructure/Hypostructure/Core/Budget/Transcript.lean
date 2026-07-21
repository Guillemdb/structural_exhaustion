import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Residual.Stage

/-!
# Framework-derived B1-B4 resource transcripts

The author registers resource operations and their primitive laws.  Core
derives the four reusable budget consequences.  These are mathematical
resource statements and never mention verifier check counts.
-/

namespace Hypostructure.Core

universe u v w uPrevious

/-- The laws supplementing `ResourceBudget` for B1: decidable comparison,
monotone ceilings, and commutative accumulation. -/
structure ResourceOrderLaws (B : ResourceBudget.{u}) where
  decideLE : forall left right : B.Resource, Decidable (left <= right)
  ceiling_monotone : forall {small large : Nat}, small <= large ->
    B.ceiling small <= B.ceiling large
  add_comm : forall left right, B.add left right = B.add right left

/-- Primitive binary bounded-composition data for B2.  Binary composition is
the reusable bounded-arity kernel; repeated bounded composition is obtained by
iterating it in the accumulated ledger. -/
structure BoundedResourceComposition (B : ResourceBudget.{u})
    (Constructor : Type v) (Equivalent : Constructor -> Constructor -> Prop)
    (representation :
      ResourceRepresentationInvariant B Constructor Equivalent) where
  compose : Constructor -> Constructor -> Constructor
  overhead : B.Resource
  enlarge : Nat -> Nat
  classMultiplier : Nat
  classOffset : Nat
  enlarge_bound : forall size,
    enlarge size <= classMultiplier * size + classOffset
  cost_compose_le : forall left right,
    representation.cost (compose left right) <=
      B.add (B.add (representation.cost left) (representation.cost right))
        overhead
  ceiling_absorbs : forall {size} {left right},
    representation.cost left <= B.ceiling size ->
    representation.cost right <= B.ceiling size ->
      B.add (B.add (representation.cost left) (representation.cost right))
          overhead <= B.ceiling (enlarge size)

namespace ResourceTranscript

/-- One represented constructor is affordable at the stated ceiling. -/
def Affordable {B : ResourceBudget.{u}} {Constructor : Type v}
    {Equivalent : Constructor -> Constructor -> Prop}
    (representation :
      ResourceRepresentationInvariant B Constructor Equivalent)
    (size : Nat) (constructor : Constructor) : Prop :=
  representation.cost constructor <= B.ceiling size

/-- Static affordability for B4. -/
def StaticAffordable {B : ResourceBudget.{u}} {Static Dynamic : Type w}
    (comparison : StaticDynamicComparison B Static Dynamic)
    (size : Nat) (value : Static) : Prop :=
  comparison.staticCost value <= B.ceiling size

/-- Dynamic affordability for B4. -/
def DynamicAffordable {B : ResourceBudget.{u}} {Static Dynamic : Type w}
    (comparison : StaticDynamicComparison B Static Dynamic)
    (size : Nat) (value : Dynamic) : Prop :=
  comparison.dynamicCost value <= B.ceiling size

/-- Primitive registrations from which Core derives B1-B4. -/
structure Input (B : ResourceBudget.{u})
    (Constructor : Type v) (Equivalent : Constructor -> Constructor -> Prop)
    (Static Dynamic : Type w) where
  order : ResourceOrderLaws B
  representation :
    ResourceRepresentationInvariant B Constructor Equivalent
  composition :
    BoundedResourceComposition B Constructor Equivalent representation
  staticDynamic : StaticDynamicComparison B Static Dynamic

/-- The framework-owned B1-B4 transcript.  Its private constructor prevents an
application from supplying already-derived affordability conclusions. -/
structure Transcript {B : ResourceBudget.{u}}
    {Constructor : Type v} {Equivalent : Constructor -> Constructor -> Prop}
    {Static Dynamic : Type w}
    (input : Input B Constructor Equivalent Static Dynamic) where
  private mk ::
  b1Decidable : forall left right : B.Resource, Decidable (left <= right)
  b1CeilingMonotone : forall {small large}, small <= large ->
    B.ceiling small <= B.ceiling large
  b1AccumulationMonotone : forall {a b c d : B.Resource},
    a <= b -> c <= d -> B.add a c <= B.add b d
  b1AccumulationCommutative : forall left right,
    B.add left right = B.add right left
  b2Composition : forall {size} {left right},
    Affordable input.representation size left ->
    Affordable input.representation size right ->
      Affordable input.representation (input.composition.enlarge size)
        (input.composition.compose left right)
  b2ClassBound : forall size,
    input.composition.enlarge size <=
      input.composition.classMultiplier * size +
        input.composition.classOffset
  b3Representation : forall {size} {left right},
    Equivalent left right ->
      (Affordable input.representation size left <->
        Affordable input.representation size right)
  b4StaticDynamic : forall {size} {static : Static} {dynamic : Dynamic},
    input.staticDynamic.comparable static dynamic ->
    StaticAffordable input.staticDynamic size static ->
      DynamicAffordable input.staticDynamic size dynamic

/-- Derive the complete B1-B4 transcript from registered primitive laws. -/
def derive {B : ResourceBudget.{u}}
    {Constructor : Type v} {Equivalent : Constructor -> Constructor -> Prop}
    {Static Dynamic : Type w}
    (input : Input B Constructor Equivalent Static Dynamic) :
    Transcript input where
  b1Decidable := input.order.decideLE
  b1CeilingMonotone := input.order.ceiling_monotone
  b1AccumulationMonotone := B.addMono
  b1AccumulationCommutative := input.order.add_comm
  b2Composition := by
    intro size left right leftAffordable rightAffordable
    exact B.leTrans
      (input.composition.cost_compose_le left right)
      (input.composition.ceiling_absorbs leftAffordable rightAffordable)
  b2ClassBound := input.composition.enlarge_bound
  b3Representation := by
    intro size left right equivalent
    unfold Affordable
    rw [input.representation.cost_eq equivalent]
  b4StaticDynamic := by
    intro size static dynamic related staticAffordable
    exact B.leTrans (input.staticDynamic.transfer related) staticAffordable

/-- Core node that installs the derived row-3 transcript in its predecessor. -/
def registrationNode {Previous : Sort uPrevious}
    {B : ResourceBudget.{u}}
    {Constructor : Type v} {Equivalent : Constructor -> Constructor -> Prop}
    {Static Dynamic : Type w}
    (input : Input B Constructor Equivalent Static Dynamic) :
    Residual.StageNode Previous (fun _ => Transcript input) :=
  Residual.StageNode.create fun _ => derive input

/-- Register row 3 through the generic accumulated-ledger executor. -/
def register {Previous : Sort uPrevious}
    {B : ResourceBudget.{u}}
    {Constructor : Type v} {Equivalent : Constructor -> Constructor -> Prop}
    {Static Dynamic : Type w}
    (input : Input B Constructor Equivalent Static Dynamic)
    (previous : Previous) :=
  (registrationNode input).run previous

@[simp]
theorem register_previous {Previous : Sort uPrevious}
    {B : ResourceBudget.{u}}
    {Constructor : Type v} {Equivalent : Constructor -> Constructor -> Prop}
    {Static Dynamic : Type w}
    (input : Input B Constructor Equivalent Static Dynamic)
    (previous : Previous) :
    (register input previous).previous = previous :=
  rfl

end ResourceTranscript

end Hypostructure.Core
