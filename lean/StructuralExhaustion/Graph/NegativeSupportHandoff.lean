import Mathlib.Tactic
import StructuralExhaustion.Graph.AssignedSupportCharge

namespace StructuralExhaustion.Graph.NegativeSupportHandoff

open StructuralExhaustion

universe u

/-!
# Typed local handoffs from a negative graph support

This module records the graph data shared by local surplus branches.  The
support is a literal finite vertex set on one fixed `FiniteObject`; its
high-center family is computed from that set, and its negative net charge is
the exact `AssignedSupportCharge` quantity.  Connectivity is witnessed inside
the same support by supplied finite walks.

The decorated branch retains proof-carrying connector arms.  It is
parameterized by the four semantic predicates that an application derives
before the handoff (context safety, local forbidden-configuration freeness,
internal-core freeness, and replacement uncompressibility) and by its local
fan-safe relation.  Routing never manufactures any of those properties.
-/

variable {V : Type u}

/-- The vertices of `core` whose ambient degree is strictly above the cubic
baseline.  This is executable over the object's declared vertex data. -/
def highCenters (object : FiniteObject V) (core : Finset V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact core.filter fun center => 4 ≤ object.degree center

/-- Exact net-charge profile of one local support.  Every actual high center
of the support is assigned once; there is no caller-selected center family. -/
def chargeProfile (object : FiniteObject V) (core : Finset V) :
    AssignedSupportCharge.Profile object where
  core := core
  assignedCenters := highCenters object core

/-- Connectedness witnessed by paths that remain in the literal finite
support.  The definition consumes one proof-selected path per queried pair;
it does not search a graph or enumerate connected subgraphs. -/
def ConnectedOn (object : FiniteObject V) (core : Finset V) : Prop :=
  core.Nonempty ∧
    ∀ ⦃left right : V⦄, left ∈ core → right ∈ core →
      ∃ path : object.graph.Walk left right,
        path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ core

/-- Exact output of local negative-charge localization on one graph. -/
structure ConnectedNegativeSupport (object : FiniteObject V) where
  core : Finset V
  connected : ConnectedOn object core
  negative : (chargeProfile object core).netQuarterCharge < 0

namespace ConnectedNegativeSupport

variable {object : FiniteObject V} (support : ConnectedNegativeSupport object)

theorem core_nonempty : support.core.Nonempty :=
  support.connected.1

theorem connectedBy
    {left right : V} (leftMem : left ∈ support.core)
    (rightMem : right ∈ support.core) :
    ∃ path : object.graph.Walk left right,
      path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ support.core :=
  support.connected.2 leftMem rightMem

/-- The exact yes-branch witness of the high-surplus test on this support. -/
structure HighSurplusWitness where
  center : V
  center_mem : center ∈ support.core
  high : 4 ≤ object.degree center

namespace HighSurplusWitness

variable {support : ConnectedNegativeSupport object}
    (witness : support.HighSurplusWitness)

theorem center_mem_highCenters :
    witness.center ∈ highCenters object support.core := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [highCenters, witness.center_mem, witness.high]

end HighSurplusWitness

end ConnectedNegativeSupport

/-- One finite handoff arm from an actual neighbour of the decoration center
to the first vertex of the counted core.  Only the terminal may belong to the
core, and the center itself is absent from the retained arm. -/
structure Arm (object : FiniteObject V) (core : Finset V) (center : V) where
  first : V
  terminal : V
  center_adjacent : object.graph.Adj center first
  terminal_mem : terminal ∈ core
  path : object.graph.Walk first terminal
  isPath : path.IsPath
  firstEntry : ∀ vertex ∈ path.support, vertex ∈ core → vertex = terminal
  center_avoided : center ∉ path.support

namespace Arm

variable {object : FiniteObject V} {core : Finset V} {center : V}
    (arm : Arm object core center)

/-- Transport an already proved arm across an equality of counted cores.  No
path or semantic datum is rebuilt. -/
def castCore {other : Finset V} (equal : core = other) :
    Arm object other center :=
  equal ▸ arm

@[simp] theorem castCore_first {other : Finset V} (equal : core = other) :
    (arm.castCore equal).first = arm.first := by
  subst other
  rfl

@[simp] theorem castCore_terminal {other : Finset V} (equal : core = other) :
    (arm.castCore equal).terminal = arm.terminal := by
  subst other
  rfl

/-- Primitive inspection count for a retained arm. -/
def checks : Nat := arm.path.support.length + 2

theorem checks_linear : arm.checks ≤ arm.path.support.length + 2 :=
  le_rfl

end Arm

/-- Exact decorated exit-handoff data.  All branch semantics remain explicit
fields.  In particular, a fan-safe response is never inferred from mere
high degree, and no property of an ordinary surplus branch is imported into
this decorated branch. -/
structure DecoratedHandoff
    (object : FiniteObject V)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop)
    (source : ConnectedNegativeSupport object) where
  source_has_no_high_center : highCenters object source.core = ∅
  center : V
  center_high : 4 ≤ object.degree center
  firstNeighbors : Finset V
  firstNeighbors_nonempty : firstNeighbors.Nonempty
  arm : (first : {vertex : V // vertex ∈ firstNeighbors}) →
    Arm object source.core center
  arm_first : ∀ first, (arm first).first = first.1
  pairwiseFanSafe : ∀ ⦃left right : V⦄,
    left ∈ firstNeighbors → right ∈ firstNeighbors → left ≠ right →
      FanSafe center left right
  contextSafe : ContextSafe source.core
  forbiddenFree : ForbiddenFree source.core
  coreFree : CoreFree source.core
  uncompressible : Uncompressible source.core

namespace DecoratedHandoff

variable
  {object : FiniteObject V}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}
  {source : ConnectedNegativeSupport object}
  (handoff : DecoratedHandoff object ContextSafe ForbiddenFree CoreFree
    Uncompressible FanSafe source)

/-- Routing inspects the finite first-neighbour schedule once.  Connector
paths are proof-carrying data and are not discovered by a path search here. -/
def routeChecks : Nat := handoff.firstNeighbors.card + 1

/-- The decoration center is external to the Type A counted core: the source
has no high center, while the separator center has ambient degree at least
four. -/
theorem center_not_mem_core : handoff.center ∉ source.core := by
  intro centerMem
  have highMem : handoff.center ∈ highCenters object source.core := by
    letI : DecidableEq V := object.input.vertices.decEq
    simp [highCenters, centerMem, handoff.center_high]
  rw [handoff.source_has_no_high_center] at highMem
  simp at highMem

theorem routeChecks_linear :
    handoff.routeChecks ≤ handoff.firstNeighbors.card + 1 :=
  le_rfl

end DecoratedHandoff

end StructuralExhaustion.Graph.NegativeSupportHandoff
