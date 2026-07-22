import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Graph.InducedPathWindowLedger

/-!
# Generic induced-path incidence and corridor contracts

This module owns the data shaping used by cold induced-path branches.  The
path order, regularity baseline, transit prefix, target predicate, and local
event semantics remain contract parameters.  No theorem-specific path order
or numerical budget is built into the graph layer.
-/

namespace Hypostructure.Graph.InducedPathCold

open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathMaximalPacking

universe u

abbrev Window (object : FiniteObject.{u}) (order : Nat) :=
  InducedPathMaximalPacking.Window object order

def support {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact InducedPathMaximalPacking.support object order window

def externalNeighbors {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.vertexFinset.filter (fun vertex =>
    object.graph.Adj (window position) vertex) \ support window

theorem externalNeighbors_mem_iff {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) (vertex : object.Vertex) :
    vertex ∈ externalNeighbors window position ↔
      object.graph.Adj (window position) vertex ∧ vertex ∉ support window := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp [externalNeighbors]

abbrev Token (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) :=
  Sigma fun position : Fin order =>
    {vertex : object.Vertex // vertex ∈ externalNeighbors window position}

noncomputable def tokenSchedule {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Enumeration (Token object order window) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (Token object order window) := inferInstance
  letI : DecidableEq (Token object order window) := inferInstance
  exact Enumeration.ofFinEnum (inferInstance : FinEnum (Token object order window))

@[simp] theorem tokenSchedule_card {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) :
    (tokenSchedule window).card =
      ∑ position : Fin order, (externalNeighbors window position).card := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (Token object order window) := inferInstance
  change (Enumeration.ofFinEnum
      (inferInstance : FinEnum (Token object order window))).card = _
  rw [Enumeration.card_ofFinEnum, FinEnum.card_eq_fintypeCard]
  simp [Token, Fintype.card_sigma]

noncomputable def branchExcess {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat) :
    List (Token object order window) :=
  (tokenSchedule window).values.drop transit

theorem branchExcess_length {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat)
    (_transit_le : transit ≤ (tokenSchedule window).card) :
    (branchExcess window transit).length =
      (tokenSchedule window).card - transit := by
  simp [branchExcess, Enumeration.card]

theorem branchExcess_nodup {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat) :
    (branchExcess window transit).Nodup := by
  exact (tokenSchedule window).nodup.drop

structure Regularity (object : FiniteObject.{u}) (order baseline : Nat)
    (window : Window object order) where
  degree_eq : ∀ position : Fin order, object.degree (window position) = baseline

noncomputable def regularityDecidable {object : FiniteObject.{u}} {order baseline : Nat}
    (window : Window object order) : Decidable (Regularity object order baseline window) := by
  exact Classical.propDecidable _

noncomputable def branchExcessChecks {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Nat :=
  (tokenSchedule window).card

theorem branchExcessChecks_linear {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) :
    branchExcessChecks window ≤ (tokenSchedule window).card := le_rfl

/-! A corridor is a graph-owned finite stage schedule.  The return-path
construction is intentionally a contract input: graph theory proves the
schedule and its path laws, while Core/CT machinery scans its events. -/
structure Corridor (object : FiniteObject.{u}) (Item : Type u) where
  items : Enumeration Item
  stages : Item -> Enumeration object.Vertex
  rootLength : Item -> Nat
  target : Nat -> Prop
  target_decidable : DecidablePred target
  rejected : ∀ item, Not (target (rootLength item))

def corridorEvents {object : FiniteObject.{u}} {Item : Type u}
    (corridor : Corridor object Item) :
    Core.Finite.ScheduleEvents.Contract Item where
  schedule := corridor.items
  Output := fun _item => Enumeration object.Vertex
  run := corridor.stages

/-! ## Focused corridor execution surface -/

/-- Build the Core schedule-event executor for a graph corridor whose graph
object and stage producer are read from the active residual.  Graph supplies
only graph-typed stage outputs; Core owns the schedule scan, hit/no-hit split,
and downstream routing. -/
def focusedCorridorEvents {Previous : Type u}
    {focus : _root_.Hypostructure.Core.Residual.Focus.Profile Previous}
    (object :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => FiniteObject.{u})
    (Item : Type u)
    (items :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => Enumeration Item)
    (stages :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun previous active =>
          (item : Item) -> Enumeration ((object.read previous active).Vertex))
    (event : (previous : Previous) -> (active : focus.Active previous) ->
      (item : Item) -> Enumeration ((object.read previous active).Vertex) ->
        Prop)
    (eventDecidable :
      (previous : Previous) -> (active : focus.Active previous) ->
        (item : Item) ->
          Decidable (event previous active item
            ((stages.read previous active) item))) :
    Core.Finite.ScheduleEvents.FocusedContract focus :=
  Core.Finite.ScheduleEvents.focusedFromQueries Item items
    (fun previous active _item =>
      Enumeration ((object.read previous active).Vertex))
    stages event eventDecidable

end Hypostructure.Graph.InducedPathCold
