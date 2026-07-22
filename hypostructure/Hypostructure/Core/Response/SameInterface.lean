import Hypostructure.Core.Residual.Focus

/-!
# Same-interface replacement packages

Core records and retrieves same-interface replacement packages without knowing
whether the package is graph-theoretic, PDE-analytic, or another domain's
response object.  The domain contract supplies the package carrier and the
item-indexed package query; Core owns the focused ledger registration.
-/

namespace Hypostructure.Core.Response.SameInterface

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious uItem uPackage uResult

/-- Optional canonical shape for domains whose replacement package consists
of source, replacement, interface, table, and completeness evidence. -/
structure BasicPackage where
  Source : Type
  Replacement : Type
  Interface : Type
  Table : Type
  source : Source
  replacement : Replacement
  interface : Interface
  table : Table
  boundaryCompatible : Prop
  sameResponse : Prop
  targetComplete : Prop

/-- Canonical proof-carrying same-interface package shape.  The carrier
types and proofs remain domain supplied, while Core can project the standard
compatibility/completeness obligations uniformly for graph and PDE uses. -/
structure VerifiedPackage where
  Source : Type
  Replacement : Type
  Interface : Type
  Table : Type
  source : Source
  replacement : Replacement
  interface : Interface
  table : Table
  boundaryCompatible : Prop
  sameResponse : Prop
  targetComplete : Prop
  boundaryCompatibleProof : boundaryCompatible
  sameResponseProof : sameResponse
  targetCompleteProof : targetComplete

namespace VerifiedPackage

theorem boundaryCompatible_verified (package : VerifiedPackage) :
    package.boundaryCompatible :=
  package.boundaryCompatibleProof

theorem sameResponse_verified (package : VerifiedPackage) :
    package.sameResponse :=
  package.sameResponseProof

theorem targetComplete_verified (package : VerifiedPackage) :
    package.targetComplete :=
  package.targetCompleteProof

end VerifiedPackage

/-- Public registration contract for item-indexed same-interface packages on
an active residual.  `Package` is abstract: Core never inspects graph/PDE
fields. -/
structure Contract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type uItem
  Package : Type uPackage
  items : Focus.ActiveQuery focus fun _previous _active => List Item
  package :
    Focus.ActiveQuery focus fun previous active =>
      (item : Item) -> item ∈ items.read previous active -> Package

namespace Contract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : Contract focus)

/-- Framework-owned schedule-wide package registration. -/
structure Certificate (previous : Previous) (active : focus.Active previous) where
  package :
    (item : contract.Item) ->
      item ∈ contract.items.read previous active -> contract.Package
  exact : package = contract.package.read previous active

abbrev Stage :=
  Focus.Stage focus fun previous active =>
    contract.Certificate previous active

/-- Register the package query as one proof-only focused extension. -/
def registerCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    { package := contract.package.read previous active
      exact := rfl }

def register (previous : Previous) : contract.Stage :=
  (contract.registerCounted previous).value

/-- Public executor spelling used by CT-facing code. -/
abbrev run (previous : Previous) : contract.Stage :=
  contract.register previous

@[simp] theorem register_previous (previous : Previous) :
    (contract.register previous).previous = previous :=
  Focus.runCounted_previous focus previous _

@[simp] theorem run_previous (previous : Previous) :
    (contract.run previous).previous = previous :=
  contract.register_previous previous

theorem registerCounted_checks (previous : Previous) :
    (contract.registerCounted previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    contract.Certificate previous active

/-- Retrieve the registered package function from the latest ledger
extension. -/
def latestPackage :
    Focus.ActiveQuery contract.successor fun stage active =>
      (item : contract.Item) ->
        item ∈ contract.items.read stage.previous active -> contract.Package :=
  (Focus.ActiveQuery.latest).map fun _stage _active certificate =>
    certificate.package

/-- Exact evidence that the latest package function is the predecessor-owned
package query. -/
def latestPackageExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.latestPackage.read stage active =
        contract.package.read stage.previous active :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    (Focus.ActiveQuery.latest.read stage active).exact

/-- Read one selected package using item and membership queries owned by the
same focused residual.  This is the standard replacement for downstream
nodes manually threading schedule membership proofs. -/
def latestPackageAt
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active) :
    Focus.ActiveQuery contract.successor fun _stage _active =>
      contract.Package :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    contract.latestPackage.read stage active
      (item.read stage active) (member.read stage active)

/-- Project a non-dependent value from a selected package while keeping
package retrieval inside the framework query API. -/
def latestPackageValue
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active)
    (Result : Sort uResult) (project : contract.Package -> Result) :
    Focus.ActiveQuery contract.successor fun _stage _active => Result :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    project ((contract.latestPackageAt item member).read stage active)

/-- Project a proof-valued obligation from a selected package. -/
def latestPackageProof
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active)
    (property : contract.Package -> Prop)
    (prove : (package : contract.Package) -> property package) :
    Focus.ActiveQuery contract.successor fun stage active =>
      property ((contract.latestPackageAt item member).read stage active) :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    prove ((contract.latestPackageAt item member).read stage active)

@[simp] theorem latestPackage_read_active (previous : Previous)
    (active : focus.Active previous) :
    contract.latestPackage.read
        (Ledger.extend previous
          (.active active
            ({ package := contract.package.read previous active
               exact := rfl } :
              contract.Certificate previous active)))
        active =
      contract.package.read previous active :=
  rfl

end Contract

/-! ## Verified package API -/

/-- Public contract for the standard proof-carrying same-interface package
shape.  This is the minimal Core API for downstream nodes that need to retrieve
boundary compatibility, same-response, and target-completeness evidence without
knowing graph or PDE internals. -/
structure VerifiedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type uItem
  items : Focus.ActiveQuery focus fun _previous _active => List Item
  package :
    Focus.ActiveQuery focus fun previous active =>
      (item : Item) -> item ∈ items.read previous active -> VerifiedPackage

namespace VerifiedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : VerifiedContract focus)

/-- Forget the verified shape to the abstract same-interface registration
contract. -/
def toContract : Contract focus where
  Item := contract.Item
  Package := VerifiedPackage
  items := contract.items
  package := contract.package

abbrev Stage :=
  (contract.toContract).Stage

abbrev successor : Focus.Profile contract.Stage :=
  (contract.toContract).successor

def registerCounted (previous : Previous) : Counted contract.Stage :=
  (contract.toContract).registerCounted previous

def register (previous : Previous) : contract.Stage :=
  (contract.toContract).register previous

abbrev run (previous : Previous) : contract.Stage :=
  contract.register previous

@[simp] theorem register_previous (previous : Previous) :
    (contract.register previous).previous = previous :=
  (contract.toContract).register_previous previous

@[simp] theorem run_previous (previous : Previous) :
    (contract.run previous).previous = previous :=
  contract.register_previous previous

theorem registerCounted_checks (previous : Previous) :
    (contract.registerCounted previous).checks =
      focus.selectionBudget.checks previous :=
  (contract.toContract).registerCounted_checks previous

def latestPackage :
    Focus.ActiveQuery contract.successor fun stage active =>
      (item : contract.Item) ->
        item ∈ contract.items.read stage.previous active -> VerifiedPackage :=
  (contract.toContract).latestPackage

def latestPackageExact :
    Focus.ActiveQuery contract.successor fun stage active =>
      contract.latestPackage.read stage active =
        contract.package.read stage.previous active :=
  (contract.toContract).latestPackageExact

def latestPackageAt
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active) :
    Focus.ActiveQuery contract.successor fun _stage _active =>
      VerifiedPackage :=
  (contract.toContract).latestPackageAt item member

def latestBoundaryCompatible
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active) :
    Focus.ActiveQuery contract.successor fun stage active =>
      ((contract.latestPackageAt item member).read stage active).boundaryCompatible :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    ((contract.latestPackageAt item member).read stage active).boundaryCompatibleProof

def latestSameResponse
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active) :
    Focus.ActiveQuery contract.successor fun stage active =>
      ((contract.latestPackageAt item member).read stage active).sameResponse :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    ((contract.latestPackageAt item member).read stage active).sameResponseProof

def latestTargetComplete
    (item :
      Focus.ActiveQuery contract.successor fun _stage _active =>
        contract.Item)
    (member :
      Focus.ActiveQuery contract.successor fun stage active =>
        item.read stage active ∈ contract.items.read stage.previous active) :
    Focus.ActiveQuery contract.successor fun stage active =>
      ((contract.latestPackageAt item member).read stage active).targetComplete :=
  Focus.ActiveQuery.ofFunction fun stage active =>
    ((contract.latestPackageAt item member).read stage active).targetCompleteProof

end VerifiedContract

end Hypostructure.Core.Response.SameInterface
