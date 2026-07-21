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

/-- The vertices of `core` whose ambient degree reaches a caller-supplied
threshold.  This is executable over the object's declared vertex data and is
the framework-owned primitive for high/low support splits. -/
def highCentersAtLeast (object : FiniteObject V) (threshold : Nat)
    (core : Finset V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact core.filter fun center => threshold ≤ object.degree center

/-- Baseline-relative specialization of `highCentersAtLeast`: strictly above
`baseline` means degree at least `baseline + 1`. -/
def highCentersAbove (object : FiniteObject V) (baseline : Nat)
    (core : Finset V) : Finset V :=
  highCentersAtLeast object (baseline + 1) core

/-- Problem-specific compatibility alias for the current Problem 64
quarter-charge profile. New framework users should choose their threshold
explicitly via `highCentersAtLeast` or `highCentersAbove`. -/
def highCenters (object : FiniteObject V) (core : Finset V) : Finset V :=
  highCentersAtLeast object 4 core

/-- Exact net-charge profile of one local support.  Every actual high center
of the support is assigned once; there is no caller-selected center family. -/
def chargeProfile (object : FiniteObject V) (core : Finset V) :
    AssignedSupportCharge.Profile object where
  core := core
  assignedCenters := highCenters object core

/-- Exact net-charge profile of one local support at a caller-supplied high
threshold.  This is the parameterized framework primitive; applications
instantiate the threshold that their obstruction/baseline requires. -/
def chargeProfileAtLeast (object : FiniteObject V) (threshold : Nat)
    (core : Finset V) : AssignedSupportCharge.Profile object where
  core := core
  assignedCenters := highCentersAtLeast object threshold core

/-- Parameterized net-charge profile of one local support.  The graph layer
does not choose the degree baseline, charge scale, or high threshold. -/
def chargeProfileWith (object : FiniteObject V)
    (parameters : AssignedSupportCharge.Parameters) (threshold : Nat)
    (core : Finset V) :
    AssignedSupportCharge.ParameterizedProfile object parameters where
  core := core
  assignedCenters := highCentersAtLeast object threshold core

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

/-- Exact output of local negative-charge localization at an explicit
high-center threshold.  This is the reusable support carrier used by generic
routes; no degree threshold is hidden in the type. -/
structure ConnectedNegativeSupportAtLeast (object : FiniteObject V)
    (threshold : Nat) where
  core : Finset V
  connected : ConnectedOn object core
  negative : (chargeProfileAtLeast object threshold core).netQuarterCharge < 0

/-- Exact output of local negative-charge localization with all reusable
numeric choices explicit. -/
structure ConnectedNegativeSupportWith (object : FiniteObject V)
    (parameters : AssignedSupportCharge.Parameters) (threshold : Nat) where
  core : Finset V
  connected : ConnectedOn object core
  negative : (chargeProfileWith object parameters threshold core).netCharge < 0

/-- Generic signed-budget entry for a support.  The framework owns the
carrier and transport; the application supplies the scale-specific
negative-budget theorem appropriate to its charge normalization. -/
structure SignedBudgetEntry
    (deficiency : Nat) (size scale : Nat) : Type where
  negativeBudget :
    (scale : Int) * (deficiency : Int) - (size : Int) < 0

/-- Package a problem-specific signed-budget proof without changing the
support or branch. -/
def signedBudgetEntry (deficiency size scale : Nat)
    (negativeBudget :
      (scale : Int) * (deficiency : Int) - (size : Int) < 0) :
    SignedBudgetEntry deficiency size scale where
  negativeBudget := negativeBudget

namespace ConnectedNegativeSupportAtLeast

variable {object : FiniteObject V} {threshold : Nat}
    (support : ConnectedNegativeSupportAtLeast object threshold)

theorem core_nonempty : support.core.Nonempty :=
  support.connected.1

theorem connectedBy
    {left right : V} (leftMem : left ∈ support.core)
    (rightMem : right ∈ support.core) :
    ∃ path : object.graph.Walk left right,
      path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ support.core :=
  support.connected.2 leftMem rightMem

/-- Generic high-surplus witness relative to this support's threshold. -/
structure HighSurplusWitness where
  center : V
  center_mem : center ∈ support.core
  high : threshold ≤ object.degree center

/-- Framework-owned yes predicate for the thresholded high-surplus split. -/
def HasHighSurplus : Prop :=
  (highCentersAtLeast object threshold support.core).Nonempty

/-- Framework-owned no predicate for the thresholded high-surplus split. -/
def NoHighSurplus : Prop :=
  highCentersAtLeast object threshold support.core = ∅

instance hasHighSurplusDecidable :
    Decidable support.HasHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold HasHighSurplus
  infer_instance

instance noHighSurplusDecidable :
    Decidable support.NoHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold NoHighSurplus
  infer_instance

/-- Convert the executable high-center scan into the exact support-indexed
witness consumed by the high branch. -/
noncomputable def highSurplusWitnessOfHasHigh
    (high : support.HasHighSurplus) : support.HighSurplusWitness := by
  classical
  let center := high.choose
  have centerMember := high.choose_spec
  have filtered := Finset.mem_filter.mp centerMember
  exact {
    center := center
    center_mem := filtered.1
    high := filtered.2
  }

/-- Complement theorem for the thresholded high/no-high split. -/
theorem noHighSurplus_of_not_hasHigh
    (notHigh : ¬ support.HasHighSurplus) : support.NoHighSurplus := by
  unfold HasHighSurplus NoHighSurplus at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

theorem assignedSurplus_eq_zero_of_noHigh
    (noHigh : support.NoHighSurplus) :
    (chargeProfileAtLeast object threshold support.core).assignedSurplus = 0 := by
  unfold NoHighSurplus at noHigh
  unfold chargeProfileAtLeast
  simp [Graph.AssignedSupportCharge.Profile.assignedSurplus, noHigh]

/-- Generic no-high consequence: if the ambient minimum degree is at least
`baseline` and the support has no vertex reaching this support's
`threshold = baseline + 1`, every support vertex has ambient degree exactly
`baseline`. -/
theorem ambientDegree_eq_baseline_of_noHigh (baseline : Nat)
    (threshold_eq : threshold = baseline + 1)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplus) :
    ∀ vertex ∈ support.core, object.degree vertex = baseline := by
  intro vertex member
  have lower : baseline ≤ object.degree vertex :=
    minimumDegreeBaseline.trans (object.minDegree_le_degree vertex)
  have notHigh : ¬ threshold ≤ object.degree vertex := by
    intro high
    have highMember : vertex ∈ highCentersAtLeast object threshold support.core := by
      letI : DecidableEq V := object.input.vertices.decEq
      simp [highCentersAtLeast, member, high]
    unfold NoHighSurplus at noHigh
    rw [noHigh] at highMember
    simp at highMember
  subst threshold
  omega

/-- Framework-owned graph meaning of a no-high entry at an arbitrary
baseline. -/
structure NoHighEntry (baseline : Nat)
    (threshold_eq : threshold = baseline + 1)
    (minimumDegreeBaseline : baseline ≤ object.minDegree) where
  noHigh : support.NoHighSurplus
  ambientDegree_eq_baseline :
    ∀ vertex ∈ support.core, object.degree vertex = baseline

/-- Construct the generic no-high entry from the framework branch proof. -/
def noHighEntry (baseline : Nat)
    (threshold_eq : threshold = baseline + 1)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplus) :
    support.NoHighEntry baseline threshold_eq minimumDegreeBaseline where
  noHigh := noHigh
  ambientDegree_eq_baseline :=
    support.ambientDegree_eq_baseline_of_noHigh baseline threshold_eq
      minimumDegreeBaseline noHigh

end ConnectedNegativeSupportAtLeast

namespace ConnectedNegativeSupportWith

variable {object : FiniteObject V}
    {parameters : AssignedSupportCharge.Parameters} {threshold : Nat}
    (support : ConnectedNegativeSupportWith object parameters threshold)

theorem core_nonempty : support.core.Nonempty :=
  support.connected.1

theorem connectedBy
    {left right : V} (leftMem : left ∈ support.core)
    (rightMem : right ∈ support.core) :
    ∃ path : object.graph.Walk left right,
      path.IsPath ∧ ∀ vertex ∈ path.support, vertex ∈ support.core :=
  support.connected.2 leftMem rightMem

/-- Generic high-surplus witness relative to this support's threshold. -/
structure HighSurplusWitness where
  center : V
  center_mem : center ∈ support.core
  high : threshold ≤ object.degree center

def HasHighSurplus : Prop :=
  (highCentersAtLeast object threshold support.core).Nonempty

def NoHighSurplus : Prop :=
  highCentersAtLeast object threshold support.core = ∅

instance hasHighSurplusDecidable :
    Decidable support.HasHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold HasHighSurplus
  infer_instance

instance noHighSurplusDecidable :
    Decidable support.NoHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold NoHighSurplus
  infer_instance

noncomputable def highSurplusWitnessOfHasHigh
    (high : support.HasHighSurplus) : support.HighSurplusWitness := by
  classical
  let center := high.choose
  have centerMember := high.choose_spec
  have filtered := Finset.mem_filter.mp centerMember
  exact {
    center := center
    center_mem := filtered.1
    high := filtered.2
  }

theorem noHighSurplus_of_not_hasHigh
    (notHigh : ¬ support.HasHighSurplus) : support.NoHighSurplus := by
  unfold HasHighSurplus NoHighSurplus at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

theorem assignedSurplus_eq_zero_of_noHigh
    (noHigh : support.NoHighSurplus) :
    (chargeProfileWith object parameters threshold
      support.core).assignedSurplus = 0 := by
  unfold NoHighSurplus at noHigh
  unfold chargeProfileWith
  let profile :
      AssignedSupportCharge.ParameterizedProfile object parameters := {
    core := support.core
    assignedCenters := highCentersAtLeast object threshold support.core
  }
  exact profile.assignedSurplus_eq_zero_of_assignedCenters_empty noHigh

theorem ambientDegree_eq_baseline_of_noHigh
    (threshold_eq : threshold = parameters.baseline + 1)
    (minimumDegreeBaseline : parameters.baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplus) :
    ∀ vertex ∈ support.core, object.degree vertex = parameters.baseline := by
  intro vertex member
  have lower : parameters.baseline ≤ object.degree vertex :=
    minimumDegreeBaseline.trans (object.minDegree_le_degree vertex)
  have notHigh : ¬ threshold ≤ object.degree vertex := by
    intro high
    have highMember : vertex ∈ highCentersAtLeast object threshold support.core := by
      letI : DecidableEq V := object.input.vertices.decEq
      simp [highCentersAtLeast, member, high]
    unfold NoHighSurplus at noHigh
    rw [noHigh] at highMember
    simp at highMember
  subst threshold
  omega

structure NoHighEntry
    (threshold_eq : threshold = parameters.baseline + 1)
    (minimumDegreeBaseline : parameters.baseline ≤ object.minDegree) where
  noHigh : support.NoHighSurplus
  ambientDegree_eq_baseline :
    ∀ vertex ∈ support.core, object.degree vertex = parameters.baseline

def noHighEntry
    (threshold_eq : threshold = parameters.baseline + 1)
    (minimumDegreeBaseline : parameters.baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplus) :
    support.NoHighEntry threshold_eq minimumDegreeBaseline where
  noHigh := noHigh
  ambientDegree_eq_baseline :=
    support.ambientDegree_eq_baseline_of_noHigh threshold_eq
      minimumDegreeBaseline noHigh

end ConnectedNegativeSupportWith

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

/-- Generic high-surplus witness relative to an arbitrary baseline. -/
structure HighSurplusWitnessAbove (baseline : Nat) where
  center : V
  center_mem : center ∈ support.core
  high : baseline + 1 ≤ object.degree center

/-- Generic high-surplus witness relative to an explicit threshold. -/
structure HighSurplusWitnessAtLeast (threshold : Nat) where
  center : V
  center_mem : center ∈ support.core
  high : threshold ≤ object.degree center

namespace HighSurplusWitness

variable {support : ConnectedNegativeSupport object}
    (witness : support.HighSurplusWitness)

theorem center_mem_highCenters :
    witness.center ∈ highCenters object support.core := by
  letI : DecidableEq V := object.input.vertices.decEq
  simp [highCenters, highCentersAtLeast, witness.center_mem, witness.high]

end HighSurplusWitness

/-- Framework-owned yes predicate for the Type-B high-surplus split. -/
def HasHighSurplus : Prop :=
  (highCenters object support.core).Nonempty

/-- Framework-owned no predicate for the Type-A no-high-surplus split. -/
def NoHighSurplus : Prop :=
  highCenters object support.core = ∅

/-- Generic framework-owned yes predicate for a high-surplus split above an
arbitrary baseline. -/
def HasHighSurplusAbove (baseline : Nat) : Prop :=
  (highCentersAbove object baseline support.core).Nonempty

/-- Generic framework-owned no predicate for a high-surplus split above an
arbitrary baseline. -/
def NoHighSurplusAbove (baseline : Nat) : Prop :=
  highCentersAbove object baseline support.core = ∅

/-- Generic framework-owned yes predicate for an explicit high threshold. -/
def HasHighSurplusAtLeast (threshold : Nat) : Prop :=
  (highCentersAtLeast object threshold support.core).Nonempty

/-- Generic framework-owned no predicate for an explicit high threshold. -/
def NoHighSurplusAtLeast (threshold : Nat) : Prop :=
  highCentersAtLeast object threshold support.core = ∅

instance hasHighSurplusDecidable : Decidable support.HasHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold HasHighSurplus
  infer_instance

instance noHighSurplusDecidable : Decidable support.NoHighSurplus := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold NoHighSurplus
  infer_instance

instance hasHighSurplusAboveDecidable (baseline : Nat) :
    Decidable (support.HasHighSurplusAbove baseline) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold HasHighSurplusAbove
  infer_instance

instance noHighSurplusAboveDecidable (baseline : Nat) :
    Decidable (support.NoHighSurplusAbove baseline) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold NoHighSurplusAbove
  infer_instance

instance hasHighSurplusAtLeastDecidable (threshold : Nat) :
    Decidable (support.HasHighSurplusAtLeast threshold) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold HasHighSurplusAtLeast
  infer_instance

instance noHighSurplusAtLeastDecidable (threshold : Nat) :
    Decidable (support.NoHighSurplusAtLeast threshold) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold NoHighSurplusAtLeast
  infer_instance

/-- Convert the executable high-center scan into the exact support-indexed
witness consumed by Type B. -/
noncomputable def highSurplusWitnessOfHasHigh
    (high : support.HasHighSurplus) : support.HighSurplusWitness := by
  classical
  let center := high.choose
  have centerMember := high.choose_spec
  have filtered := Finset.mem_filter.mp centerMember
  exact {
    center := center
    center_mem := filtered.1
    high := filtered.2
  }

/-- Convert the generic executable high-center scan into an exact
support-indexed witness. -/
noncomputable def highSurplusWitnessAboveOfHasHigh (baseline : Nat)
    (high : support.HasHighSurplusAbove baseline) :
    support.HighSurplusWitnessAbove baseline := by
  classical
  let center := high.choose
  have centerMember := high.choose_spec
  have filtered := Finset.mem_filter.mp centerMember
  exact {
    center := center
    center_mem := filtered.1
    high := filtered.2
  }

/-- Convert the explicit-threshold executable high-center scan into an exact
support-indexed witness. -/
noncomputable def highSurplusWitnessAtLeastOfHasHigh (threshold : Nat)
    (high : support.HasHighSurplusAtLeast threshold) :
    support.HighSurplusWitnessAtLeast threshold := by
  classical
  let center := high.choose
  have centerMember := high.choose_spec
  have filtered := Finset.mem_filter.mp centerMember
  exact {
    center := center
    center_mem := filtered.1
    high := filtered.2
  }

/-- If the high-surplus scan fails, the same support has no high center. -/
theorem noHighSurplus_of_not_hasHigh
    (notHigh : ¬ support.HasHighSurplus) : support.NoHighSurplus := by
  unfold HasHighSurplus NoHighSurplus at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

/-- Generic complement theorem for the high/no-high split. -/
theorem noHighSurplusAbove_of_not_hasHigh (baseline : Nat)
    (notHigh : ¬ support.HasHighSurplusAbove baseline) :
    support.NoHighSurplusAbove baseline := by
  unfold HasHighSurplusAbove NoHighSurplusAbove at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

/-- Generic complement theorem for an explicit-threshold high/no-high split. -/
theorem noHighSurplusAtLeast_of_not_hasHigh (threshold : Nat)
    (notHigh : ¬ support.HasHighSurplusAtLeast threshold) :
    support.NoHighSurplusAtLeast threshold := by
  unfold HasHighSurplusAtLeast NoHighSurplusAtLeast at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

theorem assignedSurplus_eq_zero_of_noHigh
    (noHigh : support.NoHighSurplus) :
    (chargeProfile object support.core).assignedSurplus = 0 := by
  unfold NoHighSurplus at noHigh
  unfold chargeProfile
  simp [Graph.AssignedSupportCharge.Profile.assignedSurplus, noHigh]

/-- Generic no-high consequence: if the ambient minimum degree is at least
`baseline` and the support has no vertex reaching a caller-supplied
`threshold = baseline + 1`, every support vertex has ambient degree exactly
`baseline`. -/
theorem ambientDegree_eq_baseline_of_noHighAtLeast (baseline threshold : Nat)
    (threshold_eq : threshold = baseline + 1)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplusAtLeast threshold) :
    ∀ vertex ∈ support.core, object.degree vertex = baseline := by
  intro vertex member
  have lower : baseline ≤ object.degree vertex :=
    minimumDegreeBaseline.trans (object.minDegree_le_degree vertex)
  have notHigh : ¬ threshold ≤ object.degree vertex := by
    intro high
    have highMember : vertex ∈ highCentersAtLeast object threshold support.core := by
      letI : DecidableEq V := object.input.vertices.decEq
      simp [highCentersAtLeast, member, high]
    unfold NoHighSurplusAtLeast at noHigh
    rw [noHigh] at highMember
    simp at highMember
  subst threshold
  omega

/-- Baseline-relative no-high consequence. -/
theorem ambientDegree_eq_baseline_of_noHighAbove (baseline : Nat)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplusAbove baseline) :
    ∀ vertex ∈ support.core, object.degree vertex = baseline := by
  exact support.ambientDegree_eq_baseline_of_noHighAtLeast baseline
    (baseline + 1) rfl minimumDegreeBaseline
    noHigh

/-- Cubic specialization retained for the existing Problem 64 charge profile. -/
theorem ambient_cubic_of_noHigh
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (noHigh : support.NoHighSurplus) :
    ∀ vertex ∈ support.core, object.degree vertex = 3 := by
  have noHighAbove : support.NoHighSurplusAbove 3 := by
    simpa [NoHighSurplusAbove, highCentersAbove, NoHighSurplus, highCenters]
      using noHigh
  exact support.ambientDegree_eq_baseline_of_noHighAbove 3
    minimumDegreeThree noHighAbove

theorem deficiencyQuarterNegative_of_noHigh
    (noHigh : support.NoHighSurplus) :
    4 * (((chargeProfile object support.core).positiveDeficiency : Int)) -
        (support.core.card : Int) < 0 := by
  have surplusZero := support.assignedSurplus_eq_zero_of_noHigh noHigh
  have negative := support.negative
  unfold Graph.AssignedSupportCharge.Profile.netQuarterCharge at negative
  rw [surplusZero] at negative
  simpa [chargeProfile] using negative

/-- Framework-owned graph meaning of a no-high entry above an arbitrary
baseline.  This records only consequences of the exact support and branch
proof; it does not search for another support or add a new case. -/
structure NoHighEntry (baseline : Nat)
    (minimumDegreeBaseline : baseline ≤ object.minDegree) where
  noHigh : support.NoHighSurplusAbove baseline
  ambientDegree_eq_baseline :
    ∀ vertex ∈ support.core, object.degree vertex = baseline

/-- Construct the generic no-high entry from the framework branch proof. -/
def noHighEntry (baseline : Nat)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.NoHighSurplusAbove baseline) :
    support.NoHighEntry baseline minimumDegreeBaseline where
  noHigh := noHigh
  ambientDegree_eq_baseline :=
    support.ambientDegree_eq_baseline_of_noHighAbove baseline
      minimumDegreeBaseline noHigh

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
    simp [highCenters, highCentersAtLeast, centerMem, handoff.center_high]
  rw [handoff.source_has_no_high_center] at highMem
  simp at highMem

theorem routeChecks_linear :
    handoff.routeChecks ≤ handoff.firstNeighbors.card + 1 :=
  le_rfl

end DecoratedHandoff

/-- Threshold-indexed decorated exit-handoff data.  This is the generic
variant consumed by framework routes: both the source no-high proof and the
external center height use the same caller-supplied threshold. -/
structure DecoratedHandoffAtLeast
    (object : FiniteObject V)
    (threshold : Nat)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop)
    (source : ConnectedNegativeSupportAtLeast object threshold) where
  source_has_no_high_center :
    highCentersAtLeast object threshold source.core = ∅
  center : V
  center_high : threshold ≤ object.degree center
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

namespace DecoratedHandoffAtLeast

variable
  {object : FiniteObject V}
  {threshold : Nat}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}
  {source : ConnectedNegativeSupportAtLeast object threshold}
  (handoff : DecoratedHandoffAtLeast object threshold ContextSafe ForbiddenFree
    CoreFree Uncompressible FanSafe source)

/-- Routing inspects the finite first-neighbour schedule once.  Connector
paths are proof-carrying data and are not discovered by a path search here. -/
def routeChecks : Nat := handoff.firstNeighbors.card + 1

/-- The decoration center is external to the counted core for the same
threshold used by the no-high source branch. -/
theorem center_not_mem_core : handoff.center ∉ source.core := by
  intro centerMem
  have highMem : handoff.center ∈
      highCentersAtLeast object threshold source.core := by
    letI : DecidableEq V := object.input.vertices.decEq
    simp [highCentersAtLeast, centerMem, handoff.center_high]
  rw [handoff.source_has_no_high_center] at highMem
  simp at highMem

theorem routeChecks_linear :
    handoff.routeChecks ≤ handoff.firstNeighbors.card + 1 :=
  le_rfl

end DecoratedHandoffAtLeast

/-- Fully parameterized decorated exit-handoff data. -/
structure DecoratedHandoffWith
    (object : FiniteObject V)
    (parameters : AssignedSupportCharge.Parameters)
    (threshold : Nat)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop)
    (source : ConnectedNegativeSupportWith object parameters threshold) where
  source_has_no_high_center :
    highCentersAtLeast object threshold source.core = ∅
  center : V
  center_high : threshold ≤ object.degree center
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

namespace DecoratedHandoffWith

variable
  {object : FiniteObject V}
  {parameters : AssignedSupportCharge.Parameters}
  {threshold : Nat}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}
  {source : ConnectedNegativeSupportWith object parameters threshold}
  (handoff : DecoratedHandoffWith object parameters threshold ContextSafe
    ForbiddenFree CoreFree Uncompressible FanSafe source)

def routeChecks : Nat := handoff.firstNeighbors.card + 1

theorem center_not_mem_core : handoff.center ∉ source.core := by
  intro centerMem
  have highMem : handoff.center ∈
      highCentersAtLeast object threshold source.core := by
    letI : DecidableEq V := object.input.vertices.decEq
    simp [highCentersAtLeast, centerMem, handoff.center_high]
  rw [handoff.source_has_no_high_center] at highMem
  simp at highMem

theorem routeChecks_linear :
    handoff.routeChecks ≤ handoff.firstNeighbors.card + 1 :=
  le_rfl

end DecoratedHandoffWith

end StructuralExhaustion.Graph.NegativeSupportHandoff
