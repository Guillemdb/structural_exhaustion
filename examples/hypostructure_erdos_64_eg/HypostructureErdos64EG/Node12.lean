import Hypostructure.Core.Residual.ProofProjection
import Hypostructure.Graph.AtomResponse
import HypostructureErdos64EG.Node11

/-!
# Diagram node 12: context universality

This node records the definitional projection from target completeness to
equal target response in every compatible outside context.  Core extends only
the active node-11 branch; inactive sibling branches remain in the literal
predecessor ledger.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u v

/-- The original node-12 claim over one registered proper atom, any collection
of local response coordinates, and any certified target-complete quotient of
that collection. -/
abbrev Node12Claim (stage : Node11Stage.{u, v})
    (active : Node11Focus.Active stage) : Prop :=
  let registration := node11RegistrationQuery.read stage active
  forall (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous active).G)
      (system : Graph.AtomResponse.CoordinateSystem.{u, v}
        (registration.family atom) Target)
      (quotient : Graph.AtomResponse.TargetCompleteQuotient.{u, v} system)
      {left right : system.Coordinate},
    quotient.Identified left right -> system.ContextEquivalent left right

/-- Derive the paper's definitional implication from Node 11's exact latest
registration query.  The registration value is read, never copied. -/
def node12ProjectionQuery :
    Core.Residual.Focus.ActiveQuery Node11Focus.{u, v} Node12Claim.{u, v} :=
  node11RegistrationQuery.map fun _stage _active _registration =>
    fun _atom _system quotient {_left _right} identified =>
      quotient.contextUniversal_of_identified identified

/-- Exact accumulated stage emitted by Core's proof-projection executor. -/
abbrev Node12Stage :=
  Core.Residual.ProofProjection.Stage Node11Focus.{u, v} Node12Claim.{u, v}

/-- Counted node-12 execution, including the inactive outcome. -/
def node12Counted (previous : Node11Stage.{u, v}) :=
  Core.Residual.ProofProjection.executeCounted Node11Focus.{u, v}
    Node12Claim.{u, v} node12ProjectionQuery previous

/-- Apply Graph's target-completeness projection on the literal node-11
stage.  Core owns active-branch routing and ledger extension. -/
def node12 (previous : Node11Stage.{u, v}) : Node12Stage.{u, v} :=
  (node12Counted previous).value

/-- Focus inherited by the replacement node. -/
abbrev Node12Focus :=
  Core.Residual.ProofProjection.Profile Node11Focus.{u, v} Node12Claim.{u, v}

/-- Query the private Core certificate introduced by node 12. -/
def node12CertificateQuery :=
  Core.Residual.ProofProjection.latest Node11Focus.{u, v} Node12Claim.{u, v}

/-- Query the context-universality fact from the newest ledger entry. -/
def node12ContextUniversalityQuery :
    Core.Residual.Focus.ActiveQuery Node12Focus.{u, v}
      (fun stage active => Node12Claim.{u, v} stage.previous active) :=
  Core.Residual.ProofProjection.latestClaim Node11Focus.{u, v}
    Node12Claim.{u, v}

@[simp] theorem node12_previous (previous : Node11Stage.{u, v}) :
    (node12 previous).previous = previous :=
  rfl

/-- Any two coordinates identified by any target-complete quotient of a
registered atom have identical target response against every literal outside
context. -/
theorem node12_context_universal (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous.previous active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, v}
      ((node11RegistrationQuery.read stage.previous active).family atom) Target)
    (quotient : Graph.AtomResponse.TargetCompleteQuotient.{u, v} system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  node12ContextUniversalityQuery.read stage active atom system quotient identified

/-- Every local coordinate is attached to Node 11's exact registered boundary
profile rather than to an application-copied profile. -/
theorem node12_coordinate_profile_registered (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage)
    (atom : Graph.ProperBoundariedAtom
      (node4ContextAtNode10Query.read stage.previous.previous active).G)
    (system : Graph.AtomResponse.CoordinateSystem.{u, v}
      ((node11RegistrationQuery.read stage.previous active).family atom) Target)
    (coordinate : system.Coordinate) :
    system.boundaryDegreeProfile coordinate =
      Graph.BoundariedAtomProfileCertificate.boundaryDegreeProfile
        ((node11RegistrationQuery.read stage.previous active).family atom) :=
  system.in_registered_fibre coordinate

/-- Exact total work for both active and inactive outcomes. -/
@[simp] theorem node12Counted_checks_eq_one
    (previous : Node11Stage.{u, v}) :
    (node12Counted previous).checks = 1 := by
  change
    (Core.Residual.ProofProjection.executeCounted Node11Focus.{u, v}
      Node12Claim.{u, v} node12ProjectionQuery previous).checks = 1
  rw [Core.Residual.ProofProjection.executeCounted_checks]
  rfl

theorem node12Counted_work_bounded (previous : Node11Stage.{u, v}) :
    (node12Counted previous).checks <=
      (Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).coefficient *
        ((Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).size
          previous + 1) ^
            (Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).degree :=
  Core.Residual.ProofProjection.executeCounted_checks_bounded
    Node11Focus.{u, v} Node12Claim.{u, v} node12ProjectionQuery previous

@[simp] theorem node12_checks_eq_one (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage) :
    (node12CertificateQuery.read stage active).checks = 1 := by
  exact (node12CertificateQuery.read stage active).checks_eq_budget.trans rfl

/-- The single counted focus selection satisfies its Core-owned polynomial
envelope; deriving the context-universality implication adds no local check. -/
theorem node12_work_bounded (stage : Node12Stage.{u, v})
    (active : Node12Focus.Active stage) :
    (node12CertificateQuery.read stage active).checks <=
      (Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).coefficient *
        ((Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).size
          stage.previous + 1) ^
            (Core.Residual.ProofProjection.workBudget Node11Focus.{u, v}).degree :=
  (node12CertificateQuery.read stage active).work_bounded

#print axioms node12
#print axioms node12_context_universal
#print axioms node12_coordinate_profile_registered
#print axioms node12Counted_checks_eq_one
#print axioms node12Counted_work_bounded
#print axioms node12_checks_eq_one
#print axioms node12_work_bounded

end HypostructureErdos64EG
