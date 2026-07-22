import Hypostructure.Graph.BoundariedAtom

/-!
# Arbitrary local response coordinates of one boundaried atom

The original graph argument permits any collection of local target-response
coordinates attached to a proper atom.  A coordinate need not itself be a
graph: it can encode a trace length, rooted-return test, curvature test, or
other marked response datum.  The only semantic data required here are its
registered boundary-degree fibre and its target realization against every
literal outside context.

Every coordinate system is indexed by the exact profile certificate generated
for the atom.  Membership in that fibre is therefore checked once when the
system is formed.  A target-complete quotient is an arbitrary certified setoid
whose identifications preserve the target response in every outside context.
Graph derives profile preservation, the canonical exact quotient, and the
context-universality projection.
-/

namespace Hypostructure.Graph.AtomResponse

open Hypostructure.Graph

universe u v

/-- An arbitrary collection of local response coordinates for one exact
proper atom.  `realize coordinate outside` is the global finite graph whose
target response that coordinate records in the supplied outside context. -/
structure CoordinateSystem {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    (certificate : BoundariedAtomProfileCertificate atom)
    (Target : FiniteObject.{u} -> Prop) where
  Coordinate : Type v
  boundaryDegreeProfile :
    Coordinate -> BoundaryDegreeProfile atom.decomposition.interface
  realize : Coordinate ->
    OutsideContext atom.decomposition.interface -> FiniteObject.{u}
  in_registered_fibre : forall coordinate,
    boundaryDegreeProfile coordinate = certificate.boundaryDegreeProfile

namespace CoordinateSystem

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}

/-- Exact target response of one coordinate in one literal outside context. -/
def targetResponse (system : CoordinateSystem.{u, v} certificate Target)
    (coordinate : system.Coordinate)
    (outside : OutsideContext atom.decomposition.interface) : Prop :=
  Target (system.realize coordinate outside)

/-- Two arbitrary coordinates have the same target response against every
literal outside context. -/
def ContextEquivalent (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) : Prop :=
  forall outside : OutsideContext atom.decomposition.interface,
    system.targetResponse left outside <-> system.targetResponse right outside

/-- A system represented by same-boundary graph pieces is one specialization
of the arbitrary-coordinate API.  The caller proves once that each piece lies
in the atom's registered profile fibre. -/
noncomputable def ofPieces
    (Coordinate : Type v)
    (represented : Coordinate -> BoundaryPiece atom.decomposition.interface)
    (inRegisteredFibre : forall coordinate,
      (represented coordinate).boundaryDegreeProfile =
        certificate.boundaryDegreeProfile) :
    CoordinateSystem certificate Target where
  Coordinate := Coordinate
  boundaryDegreeProfile coordinate :=
    (represented coordinate).boundaryDegreeProfile
  realize coordinate outside := Graph.glue (represented coordinate) outside
  in_registered_fibre := inRegisteredFibre

@[simp] theorem targetResponse_ofPieces
    (Coordinate : Type v)
    (represented : Coordinate -> BoundaryPiece atom.decomposition.interface)
    (inRegisteredFibre : forall coordinate,
      (represented coordinate).boundaryDegreeProfile =
        certificate.boundaryDegreeProfile)
    (coordinate : Coordinate)
    (outside : OutsideContext atom.decomposition.interface) :
    (ofPieces (Target := Target) Coordinate represented
      inRegisteredFibre).targetResponse coordinate outside <->
        Target (Graph.glue (represented coordinate) outside) :=
  Iff.rfl

end CoordinateSystem

/-- A quotient of an arbitrary coordinate collection is target-complete when
every identification preserves target response against every outside context.
Boundary-profile preservation is automatic because the collection was
registered in one exact Node-11 profile fibre. -/
structure TargetCompleteQuotient
    {object : FiniteObject.{u}}
    {atom : ProperBoundariedAtom object}
    {certificate : BoundariedAtomProfileCertificate atom}
    {Target : FiniteObject.{u} -> Prop}
    (system : CoordinateSystem.{u, v} certificate Target) where
  relation : Setoid system.Coordinate
  context_complete : forall {left right}, relation.r left right ->
    system.ContextEquivalent left right

namespace TargetCompleteQuotient

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}
variable {system : CoordinateSystem.{u, v} certificate Target}

/-- The proof-relevant identification made by a certified quotient. -/
def Identified (quotient : TargetCompleteQuotient system)
    (left right : system.Coordinate) : Prop :=
  quotient.relation.r left right

/-- Actual quotient carrier generated by the certified equivalence relation. -/
abbrev Carrier (quotient : TargetCompleteQuotient system) : Type v :=
  Quotient quotient.relation

/-- Condition (a) of target completeness follows from the registered fibre
laws of the two coordinates. -/
theorem profile_preserved (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (_identified : quotient.Identified left right) :
    system.boundaryDegreeProfile left =
      system.boundaryDegreeProfile right :=
  (system.in_registered_fibre left).trans
    (system.in_registered_fibre right).symm

/-- Condition (b) of target completeness is exactly context universality. -/
theorem contextUniversal_of_identified
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  quotient.context_complete identified

end TargetCompleteQuotient

namespace CoordinateSystem

variable {object : FiniteObject.{u}}
variable {atom : ProperBoundariedAtom object}
variable {certificate : BoundariedAtomProfileCertificate atom}
variable {Target : FiniteObject.{u} -> Prop}

/-- Literal all-context response equivalence is an equivalence relation on any
arbitrary coordinate collection. -/
def exactSetoid (system : CoordinateSystem.{u, v} certificate Target) :
    Setoid system.Coordinate where
  r := system.ContextEquivalent
  iseqv := {
    refl := by
      intro coordinate outside
      rfl
    symm := by
      intro left right equivalent outside
      exact (equivalent outside).symm
    trans := by
      intro first second third firstSecond secondThird outside
      exact (firstSecond outside).trans (secondThird outside)
  }

/-- Canonical maximal target-complete quotient generated by exact response
equivalence.  Applications need not construct routing or quotient evidence. -/
def exactQuotient (system : CoordinateSystem.{u, v} certificate Target) :
    TargetCompleteQuotient system where
  relation := system.exactSetoid
  context_complete := fun identified => identified

@[simp] theorem exactQuotient_identified_iff
    (system : CoordinateSystem.{u, v} certificate Target)
    (left right : system.Coordinate) :
    (system.exactQuotient.Identified left right) <->
      system.ContextEquivalent left right :=
  Iff.rfl

end CoordinateSystem

end Hypostructure.Graph.AtomResponse
