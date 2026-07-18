import StructuralExhaustion.Graph.InducedPathColdCorridor
import StructuralExhaustion.Graph.InducedPathColdLedger
import StructuralExhaustion.Graph.InducedSubgraph

namespace StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger

universe u

variable {V : Type u} {object : FiniteObject V}

/-!
# Skeleton deletion for an explicit selected cubic-window family

Unlike `InducedPathColdSkeleton`, this profile does not silently use every
ambient-cubic member of the selected packing.  Its family is an explicit
finite set of selected window indices, with a proof that each retained index
is ambient-cubic.  This is the reusable graph layer needed when a prior
semantic classifier, such as a hot/cold split, selects only part of the
ambient-cubic packing.
-/

structure CubicWindowFamily (object : FiniteObject V) where
  windows : Finset (WindowIndex object)
  cubic : ∀ window ∈ windows, AmbientCubic object window

/-- Union of precisely the selected family's window supports. -/
noncomputable def deletedWindowVertices
    (family : CubicWindowFamily object) : Finset V := by
  classical
  exact family.windows.biUnion fun window =>
    InducedPathPacking.support object 13 (selectedWindow object window)

/-- Remainder after deleting precisely the supplied family. -/
noncomputable def outsideVertices
    (family : CubicWindowFamily object) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact object.vertexFinset \ deletedWindowVertices family

abbrev OutsideVertex (family : CubicWindowFamily object) :=
  {vertex : V // vertex ∈ outsideVertices family}

noncomputable def outsideObject (family : CubicWindowFamily object) :
    FiniteObject (OutsideVertex family) :=
  object.induceFinset (outsideVertices family)

/-- A literal incidence from a family window whose other endpoint survives
the restricted deletion. -/
structure BoundaryStub (family : CubicWindowFamily object) where
  token : Token object
  window_mem : token.1 ∈ family.windows
  outside : token.2.2.1 ∈ outsideVertices family

namespace BoundaryStub

variable {family : CubicWindowFamily object}

abbrev window (stub : BoundaryStub family) := stub.token.1
abbrev offset (stub : BoundaryStub family) := stub.token.2.1
abbrev neighbor (stub : BoundaryStub family) := stub.token.2.2.1

theorem cubic (stub : BoundaryStub family) : AmbientCubic object stub.window :=
  family.cubic stub.window stub.window_mem

def endpoint (stub : BoundaryStub family) : OutsideVertex family :=
  ⟨stub.neighbor, stub.outside⟩

end BoundaryStub

/-- Connected component of the restricted outside graph incident with one
boundary stub. -/
noncomputable def component {family : CubicWindowFamily object}
    (stub : BoundaryStub family) :
    (outsideObject family).graph.ConnectedComponent :=
  (outsideObject family).graph.connectedComponentMk stub.endpoint

/-- Two distinct boundary stubs in the same restricted outside component,
with their declared successor relation retained. -/
structure TwoStubComponent (family : CubicWindowFamily object)
    (DeclaredSuccessor : BoundaryStub family → BoundaryStub family → Prop) where
  anchor : BoundaryStub family
  successor : BoundaryStub family
  distinct : successor ≠ anchor
  sameComponent : component successor = component anchor
  declaredSuccessor : DeclaredSuccessor anchor successor

namespace TwoStubComponent

variable {family : CubicWindowFamily object}
variable {DeclaredSuccessor : BoundaryStub family → BoundaryStub family → Prop}

noncomputable def componentRoot
    (data : TwoStubComponent family DeclaredSuccessor) :
    (component data.anchor).supp := by
  refine ⟨data.anchor.endpoint, ?_⟩
  simp [component]

noncomputable def componentTarget
    (data : TwoStubComponent family DeclaredSuccessor) :
    (component data.anchor).supp := by
  refine ⟨data.successor.endpoint, ?_⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact data.sameComponent

theorem component_preconnected
    (data : TwoStubComponent family DeclaredSuccessor) :
    (component data.anchor).toSimpleGraph.Preconnected :=
  (component data.anchor).connected_toSimpleGraph.preconnected

end TwoStubComponent

/-- A supplied incidence whose endpoint belongs to the exact restricted
deletion union. -/
structure CrossWindowResidual (family : CubicWindowFamily object)
    (stub : InducedPathColdCorridor.CubicStub object) where
  stubExact : InducedPathColdCorridor.CubicStub object
  exact : stubExact = stub
  endpointDeleted : stub.neighbor ∈ deletedWindowVertices family

inductive EntryResult (family : CubicWindowFamily object)
    (stub : InducedPathColdCorridor.CubicStub object)
    (window_mem : stub.window ∈ family.windows) where
  | componentBoundary
      (boundary : BoundaryStub family)
      (tokenExact : boundary.token = stub.token)
  | crossWindow (residual : CrossWindowResidual family stub)

/-- One exact membership decision for a source stub whose own window belongs
to the declared family. -/
noncomputable def route (family : CubicWindowFamily object)
    (stub : InducedPathColdCorridor.CubicStub object)
    (window_mem : stub.window ∈ family.windows) :
    EntryResult family stub window_mem := by
  letI : DecidableEq V := object.input.vertices.decEq
  by_cases survives : stub.neighbor ∈ outsideVertices family
  · exact .componentBoundary
      ⟨stub.token, window_mem, survives⟩ rfl
  · have deleted : stub.neighbor ∈ deletedWindowVertices family := by
      by_contra notDeleted
      apply survives
      rw [outsideVertices, Finset.mem_sdiff]
      exact ⟨object.mem_vertexFinset stub.neighbor, notDeleted⟩
    exact .crossWindow ⟨stub, rfl, deleted⟩

theorem route_exhaustive (family : CubicWindowFamily object)
    (stub : InducedPathColdCorridor.CubicStub object)
    (window_mem : stub.window ∈ family.windows) :
    (∃ boundary tokenExact,
      route family stub window_mem = .componentBoundary boundary tokenExact) ∨
    (∃ residual, route family stub window_mem = .crossWindow residual) := by
  cases equation : route family stub window_mem with
  | componentBoundary boundary tokenExact =>
      exact Or.inl ⟨boundary, tokenExact, rfl⟩
  | crossWindow residual => exact Or.inr ⟨residual, rfl⟩

def visibleChecks (_family : CubicWindowFamily object)
    (_stub : InducedPathColdCorridor.CubicStub object) : Nat := 1

end StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton
