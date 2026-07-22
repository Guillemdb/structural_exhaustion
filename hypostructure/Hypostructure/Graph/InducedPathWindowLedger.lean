import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hypostructure.Graph.Finite
import Hypostructure.Graph.InducedPathMaximalPacking

/-!
# Generic induced-path window ledgers

This module derives local incidence and surplus observables from an already
selected induced-path packing profile.  The path order and baseline degree are
parameters supplied by the application contract.
-/

namespace Hypostructure.Graph.InducedPathWindowLedger

open scoped BigOperators

universe u

abbrev Window (object : FiniteObject.{u}) (order : Nat) :=
  InducedPathMaximalPacking.Window object order

abbrev WindowIndex (object : FiniteObject.{u}) (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order) :=
  {window : Window object order // window ∈ profile.selected}

def selectedWindow {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (index : WindowIndex object order profile) :
    Window object order :=
  index.1

def windowIndices {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    List (WindowIndex object order profile) :=
  profile.selected.attach

@[simp] theorem windowIndices_length {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    (windowIndices profile).length = profile.selected.length := by
  simp [windowIndices]

/-- Degree in the source path on `order` vertices. -/
def pathDegree (order : Nat) (position : Fin order) : Nat :=
  if position.val = 0 ∨ position.val + 1 = order then 1 else 2

/-- Total surplus above `baselineDegree` on all ambient vertices. -/
def totalSurplus (object : FiniteObject.{u}) (baselineDegree : Nat) : Nat :=
  (object.orderedVertices.map
    (fun vertex => object.degree vertex - baselineDegree)).sum

/-- Surplus above `baselineDegree` on selected window positions. -/
def windowSurplus (object : FiniteObject.{u}) (order baselineDegree : Nat)
    (profile : InducedPathMaximalPacking.Profile object order) : Nat :=
  ((windowIndices profile).map fun index =>
    ((List.finRange order).map fun position =>
      object.degree (selectedWindow index position) - baselineDegree).sum).sum

/-- A compact public ledger for later threshold and capacity comparisons. -/
structure Ledger (object : FiniteObject.{u}) (order baselineDegree : Nat) where
  profile : InducedPathMaximalPacking.Profile object order
  packingNumber : Nat := profile.selected.length
  totalSurplus : Nat := totalSurplus object baselineDegree
  windowSurplus : Nat := windowSurplus object order baselineDegree profile

end Hypostructure.Graph.InducedPathWindowLedger
