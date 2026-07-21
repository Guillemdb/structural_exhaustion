import Hypostructure.Core.Coordinate.Transport
import Hypostructure.Graph.Induced
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.Problem

/-!
# Primitive graph coordinates

Coordinates are the exact packed source and target graphs.  Their represented
objects are trivial because the coordinate itself already contains the graph.
Graph registers only primitive relabelling and induced restriction; Core owns
paths, composition, execution, and composite transport.
-/

namespace Hypostructure.Graph

universe u v

/-- Primitive graph operations between exact packed coordinates. -/
inductive CoordinatePrimitive :
    FiniteObject.{u} -> FiniteObject.{u} -> Type (u + 1)
  | relabel {source target : FiniteObject.{u}}
      (iso : source.Iso target) : CoordinatePrimitive source target
  | induce (source : FiniteObject.{u}) (support : Finset source.Vertex) :
      CoordinatePrimitive source (source.induce support)

/-- Register graph primitives with the domain-independent coordinate engine. -/
def coordinateSystem (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v) :
    Core.CoordinateSystem (problem Baseline BranchState) where
  Coordinate := FiniteObject.{u}
  Object := fun _ => Unit
  realize := fun coordinate _ => coordinate
  Primitive := CoordinatePrimitive
  act := fun _ _ => ()

@[simp]
theorem coordinateSystem_realize (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (coordinate : FiniteObject.{u}) (object : Unit) :
    (coordinateSystem Baseline BranchState).realize coordinate object =
      coordinate :=
  rfl

@[simp]
theorem coordinateSystem_act (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    {source target : FiniteObject.{u}}
    (step : CoordinatePrimitive source target) (object : Unit) :
    (coordinateSystem Baseline BranchState).act step object = () :=
  rfl

namespace CoordinatePrimitive

/-- A relabelling primitive realizes an isomorphic target graph. -/
theorem relabel_isomorphic {source target : FiniteObject.{u}}
    (iso : source.Iso target) : source.Isomorphic target :=
  ⟨iso⟩

/-- Baseline laws for graph primitives.  Relabelling is discharged by generic
isomorphism invariance; only induced restriction needs a problem-specific law.
-/
def baselineTransport (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (inducePreserves : forall (object : FiniteObject.{u})
      (support : Finset object.Vertex),
      Baseline object -> Baseline (object.induce support)) :
    Core.PrimitiveBaselineTransport
      (coordinateSystem Baseline BranchState) where
  preserves := by
    intro source target step object baseline
    cases step with
    | relabel iso =>
        exact baselineInvariant.transport ⟨iso⟩ baseline
    | induce support =>
        exact inducePreserves _ support baseline

/-- Branch-state laws remain theorem-specific, but their composition and path
execution are inherited from Core once these two primitive cases are supplied.
-/
def branchStateTransport (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v)
    (relabelTransport : forall {source target : FiniteObject.{u}},
      source.Isomorphic target -> BranchState source -> BranchState target)
    (induceTransport : forall (object : FiniteObject.{u})
      (support : Finset object.Vertex),
      BranchState object -> BranchState (object.induce support)) :
    Core.PrimitiveBranchStateTransport
      (coordinateSystem Baseline BranchState) where
  transport := by
    intro source target step object state
    cases step with
    | relabel iso =>
        exact relabelTransport ⟨iso⟩ state
    | induce support =>
        exact induceTransport _ support state

end CoordinatePrimitive

end Hypostructure.Graph
