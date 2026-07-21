import StructuralExhaustion.Core.FixedTwoBoundaryCutState
import StructuralExhaustion.Graph.InducedPathColdLedger
import StructuralExhaustion.Graph.InducedSubgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathColdSkeleton

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger

universe u

variable {V : Type u}

/-!
# Ambient-cubic window skeleton

This module performs only the structural part of the paper's cold-skeleton
construction: delete the supports of ambient-cubic selected P13 windows,
retain literal window--remainder incidences, group them by connected component
of the induced remainder, take the cyclic successor in the declared token
order, and retain a proof-carrying lex-first shortest component path.  The
successor and path certificates are inherited from structural producer layers;
this module does not scan the ambient stub, component, or path families.

It does not infer D4--D7 response coordinates or packed reconstruction from a
simple path.  That missing semantic projection is isolated below as one typed
residual.
-/

/-- Union of the supports of all ambient-cubic selected windows. -/
noncomputable def deletedWindowVertices (object : FiniteObject V) : Finset V := by
  classical
  letI : FinEnum (WindowIndex object) := windowIndices object
  exact Finset.univ.biUnion fun window ↦
    if AmbientCubic object window then
      InducedPathPacking.support object 13 (selectedWindow object window)
    else ∅

/-- Vertices left after deleting those window supports. -/
noncomputable def outsideVertices (object : FiniteObject V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact object.vertexFinset \ deletedWindowVertices object

abbrev OutsideVertex (object : FiniteObject V) :=
  {vertex : V // vertex ∈ outsideVertices object}

noncomputable def outsideObject (object : FiniteObject V) : FiniteObject (OutsideVertex object) :=
  object.induceFinset (outsideVertices object)

/-- A literal external incidence from an ambient-cubic window whose other end
survives in the induced remainder. -/
structure BoundaryStub (object : FiniteObject V) where
  token : Token object
  cubic : AmbientCubic object token.1
  outside : token.2.2.1 ∈ outsideVertices object

namespace BoundaryStub

variable {object : FiniteObject V}

abbrev window (stub : BoundaryStub object) : WindowIndex object := stub.token.1
abbrev offset (stub : BoundaryStub object) : Fin 13 := stub.token.2.1
abbrev neighbor (stub : BoundaryStub object) : V := stub.token.2.2.1

def endpoint (stub : BoundaryStub object) : OutsideVertex object :=
  ⟨stub.neighbor, stub.outside⟩

end BoundaryStub

/-- The induced-remainder connected component incident with a boundary stub. -/
noncomputable def component {object : FiniteObject V}
    (stub : BoundaryStub object) :
    (outsideObject object).graph.ConnectedComponent :=
  (outsideObject object).graph.connectedComponentMk stub.endpoint

/-- Proof-carrying cyclic successor chosen by the paper's inherited boundary
order.  `DeclaredSuccessor` is the structural successor relation produced by
that earlier layer; this module never scans the ambient stub family. -/
structure TwoStubComponent (object : FiniteObject V)
    (DeclaredSuccessor : BoundaryStub object → BoundaryStub object → Prop) where
  anchor : BoundaryStub object
  successor : BoundaryStub object
  distinct : successor ≠ anchor
  sameComponent : component successor = component anchor
  declaredSuccessor : DeclaredSuccessor anchor successor

namespace TwoStubComponent

variable {object : FiniteObject V}
variable {DeclaredSuccessor : BoundaryStub object → BoundaryStub object → Prop}

noncomputable def componentRoot
    (data : TwoStubComponent object DeclaredSuccessor) :
    (component data.anchor).supp := by
  refine ⟨data.anchor.endpoint, ?_⟩
  simp [component]

noncomputable def componentTarget
    (data : TwoStubComponent object DeclaredSuccessor) :
    (component data.anchor).supp := by
  refine ⟨data.successor.endpoint, ?_⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact data.sameComponent

theorem component_preconnected
    (data : TwoStubComponent object DeclaredSuccessor) :
    (component data.anchor).toSimpleGraph.Preconnected :=
  (component data.anchor).connected_toSimpleGraph.preconnected

/-- Rank used by the paper's declared lexicographic tie-break.  It is inherited
as structural data rather than computed by enumerating all component paths. -/
structure PathTieBreak (data : TwoStubComponent object DeclaredSuccessor) where
  rank : (component data.anchor).toSimpleGraph.Walk
    data.componentRoot data.componentTarget → Nat

/-- Proof-carrying lex-first shortest component path. -/
structure CanonicalComponentPath
    (data : TwoStubComponent object DeclaredSuccessor)
    (tieBreak : PathTieBreak data) where
  path : (component data.anchor).toSimpleGraph.Walk
    data.componentRoot data.componentTarget
  isPath : path.IsPath
  shortest : path.length =
    (component data.anchor).toSimpleGraph.dist
      data.componentRoot data.componentTarget
  declaredFirst : ∀ candidate :
      (component data.anchor).toSimpleGraph.Walk
        data.componentRoot data.componentTarget,
    candidate.IsPath →
    candidate.length =
      (component data.anchor).toSimpleGraph.dist
        data.componentRoot data.componentTarget →
    tieBreak.rank path ≤ tieBreak.rank candidate

/-- The structural observations which can be projected without D4--D7.  The
two interface degrees and induced-path offsets are literal, and connector
length is observed later only through the application-supplied target offset
alphabet. -/
noncomputable def observations
    (data : TwoStubComponent object DeclaredSuccessor)
    {tieBreak : PathTieBreak data}
    (canonical : CanonicalComponentPath data tieBreak) :
    Core.FixedTwoBoundaryCutState.PrefixObservations 13 Unit where
  boundaryDegree _ role :=
    if role = 0 then object.degree data.anchor.neighbor
    else object.degree data.successor.neighbor
  windowOffset _ role :=
    if role = 0 then data.anchor.offset else data.successor.offset
  connectorLength _ := canonical.path.length

/-- Fixed D4--D7 alphabet and its graph-derived local response. -/
structure DeclaredLocalSemantics
    (data : TwoStubComponent object DeclaredSuccessor)
    {tieBreak : PathTieBreak data}
    (canonical : CanonicalComponentPath data tieBreak) where
  LocalCoordinate : Type u
  coordinates : FinEnum LocalCoordinate
  localResponse : LocalCoordinate → Bool

/-- Normalized projection once the sole local semantic map is supplied. -/
noncomputable def fixedState
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    (data : TwoStubComponent object DeclaredSuccessor)
    {tieBreak : PathTieBreak data}
    (canonical : CanonicalComponentPath data tieBreak)
    (semantics : DeclaredLocalSemantics data canonical) :
    Core.FixedTwoBoundaryCutState.State 13 13 semantics.LocalCoordinate :=
  Core.FixedTwoBoundaryCutState.project LengthOK lengthOKDecidable
    (data.observations canonical)
    ⟨fun _ ↦ semantics.localResponse⟩ ()

/-- Sole honest stopping residual before repetition/CT3.  The structural
corridor is present, but no D4--D7 alphabet/response map and no literal packed
reconstruction/context-transport theorem have yet been derived. -/
structure MissingD4D7Reconstruction
    (data : TwoStubComponent object DeclaredSuccessor)
    {tieBreak : PathTieBreak data}
    (canonical : CanonicalComponentPath data tieBreak) where
  marker : Unit := ()

end TwoStubComponent

end StructuralExhaustion.Graph.InducedPathColdSkeleton
