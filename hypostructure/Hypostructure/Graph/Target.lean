import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Hypostructure.Graph.Isomorphism

/-!
# Isomorphism-invariant graph targets

Targets remain predicates separate from `Graph.problem`.  A target interface
contains exactly the representation-invariance evidence needed by Core.
Cycle targets use Mathlib walks and introduce no parallel path or cycle model.
-/

namespace Hypostructure.Graph

universe u v

/-- Minimal graph capability for transporting one external target. -/
structure TargetInterface (Target : FiniteObject.{u} → Prop) : Prop where
  isomorphismInvariant : FiniteObject.IsomorphismInvariant Target

namespace TargetInterface

/-- Convert graph target invariance to Core target invariance for any
isomorphism-invariant baseline and branch-state family. -/
def coreInvariant {Target : FiniteObject.{u} → Prop}
    (interface : TargetInterface Target)
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline) :
    Core.TargetInvariant
      (isomorphismEquivalence Baseline BranchState baselineInvariant) Target where
  target_iff := interface.isomorphismInvariant.iff_of_iso

end TargetInterface

/-- A Mathlib simple cycle whose length satisfies a caller-selected predicate. -/
structure CycleCertificate (object : FiniteObject.{u})
    (LengthOK : Nat → Prop) where
  vertex : object.Vertex
  walk : object.graph.Walk vertex vertex
  isCycle : walk.IsCycle
  length_ok : LengthOK walk.length

/-- External target asserting the existence of an accepted cycle certificate. -/
def HasCycleWithLength (LengthOK : Nat → Prop)
    (object : FiniteObject.{u}) : Prop :=
  Nonempty (CycleCertificate object LengthOK)

namespace CycleCertificate

/-- Transport a cycle certificate through an injective graph homomorphism. -/
def mapHom {left right : FiniteObject.{u}} {LengthOK : Nat -> Prop}
    (hom : left.graph →g right.graph) (injective : Function.Injective hom)
    (certificate : CycleCertificate left LengthOK) :
    CycleCertificate right LengthOK where
  vertex := hom certificate.vertex
  walk := certificate.walk.map hom
  isCycle := certificate.isCycle.map injective
  length_ok := by
    rw [SimpleGraph.Walk.length_map]
    exact certificate.length_ok

/-- Transport a cycle certificate through a concrete graph isomorphism. -/
def mapIso {left right : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (iso : left.Iso right) (certificate : CycleCertificate left LengthOK) :
    CycleCertificate right LengthOK :=
  mapHom iso.toHom iso.injective certificate

/-- Package a directly validated closed Mathlib walk. -/
def ofAccepted {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    {vertex : object.Vertex} {walk : object.graph.Walk vertex vertex}
    (accepted : walk.IsCycle ∧ LengthOK walk.length) :
    CycleCertificate object LengthOK where
  vertex := vertex
  walk := walk
  isCycle := accepted.1
  length_ok := accepted.2

end CycleCertificate

/-- Cycle-length existence is invariant under packed graph isomorphism. -/
theorem hasCycleWithLength_iff_of_iso
    {left right : FiniteObject.{u}} (iso : left.Iso right)
    (LengthOK : Nat → Prop) :
    HasCycleWithLength LengthOK left ↔
      HasCycleWithLength LengthOK right := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.mapIso iso⟩
  · rintro ⟨certificate⟩
    exact ⟨certificate.mapIso iso.symm⟩

/-- The cycle target's reusable graph target interface. -/
def cycleTargetInterface (LengthOK : Nat → Prop) :
    TargetInterface (HasCycleWithLength LengthOK) where
  isomorphismInvariant := {
    iff_of_iso := by
      intro left right equivalent
      rcases equivalent with ⟨iso⟩
      exact hasCycleWithLength_iff_of_iso iso LengthOK
  }

/-- Validation predicate for a supplied closed walk.  It is intentionally
local: the graph layer never enumerates an implicit universe of walks. -/
def AcceptsCycleLength {object : FiniteObject.{u}}
    (LengthOK : Nat → Prop) {vertex : object.Vertex}
    (walk : object.graph.Walk vertex vertex) : Prop :=
  walk.IsCycle ∧ LengthOK walk.length

/-- Decidability of the cycle condition on one supplied closed walk. -/
def isCycleDecidable {object : FiniteObject.{u}}
    {vertex : object.Vertex} (walk : object.graph.Walk vertex vertex) :
    Decidable walk.IsCycle := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  infer_instance

/-- Executable validation for a supplied closed walk and decidable length
predicate. -/
def acceptsCycleLengthDecidable {object : FiniteObject.{u}}
    (LengthOK : Nat → Prop)
    (lengthDecidable : ∀ length, Decidable (LengthOK length))
    {vertex : object.Vertex} (walk : object.graph.Walk vertex vertex) :
    Decidable (AcceptsCycleLength LengthOK walk) :=
  @instDecidableAnd walk.IsCycle (LengthOK walk.length)
    (isCycleDecidable walk) (lengthDecidable walk.length)

/-- A directly accepted walk realizes the corresponding external target. -/
theorem hasCycleWithLength_of_accepts
    {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    {vertex : object.Vertex} {walk : object.graph.Walk vertex vertex}
    (accepted : AcceptsCycleLength LengthOK walk) :
    HasCycleWithLength LengthOK object :=
  ⟨CycleCertificate.ofAccepted accepted⟩

end Hypostructure.Graph
