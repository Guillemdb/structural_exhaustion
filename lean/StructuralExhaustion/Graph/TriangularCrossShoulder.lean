import Mathlib.Tactic
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Graph.TriangularFirstLanding

namespace StructuralExhaustion.Graph.TriangularCrossShoulder

open StructuralExhaustion

universe u

/-!
# CT9 cross-shoulder multiplicity

For two fixed distinct triangular ports, the candidate universe is the four
ordered shoulder pairs.  Actual cross edges form one capacity-one CT9 fibre.
Two distinct edges either share a shoulder, forcing that shoulder to have
degree at least four, or are vertex-disjoint and form a literal four-cycle.
Thus four-cycle avoidance leaves exactly the manuscript split: a high shoulder
is routed out, or the fibre is bounded by one.
-/

abbrev Setup
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) :=
  TriangularShoulderCompletion.Setup base object baseline center

abbrev TriPort
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  TriangularShoulderCompletion.TriPort setup

def site
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (port : TriPort setup) (side : Bool) :
    TriangularShoulderCompletion.Site setup :=
  (port, side)

def shoulder
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (port : TriPort setup) (side : Bool) : V :=
  TriangularShoulderCompletion.shoulder setup (site port side)

abbrev Candidate := Bool × Bool

def IsCrossEdge
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (candidate : Candidate) : Prop :=
  object.graph.Adj (shoulder first candidate.1)
    (shoulder second candidate.2)

abbrev CrossEdge
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) :=
  {candidate : Candidate // IsCrossEdge first second candidate}

@[implicit_reducible]
def candidates : FinEnum Candidate :=
  Core.Enumeration.prod Core.Enumeration.bool Core.Enumeration.bool

@[implicit_reducible]
def crossEdges
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : FinEnum (CrossEdge first second) := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact Core.Enumeration.subtype candidates (IsCrossEdge first second)
    (fun _candidate => by
      unfold IsCrossEdge
      infer_instance)

theorem shoulder_injective
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (port : TriPort setup) {left right : Bool}
    (equal : shoulder port left = shoulder port right) : left = right := by
  cases left <;> cases right
  · rfl
  · exact (TriangularShoulderCompletion.shoulder_ne_other setup
      (site port false) equal).elim
  · exact (TriangularShoulderCompletion.shoulder_ne_other setup
      (site port true) equal).elim
  · rfl

theorem shoulder_adjacent_of_ne
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (port : TriPort setup) {left right : Bool} (different : left ≠ right) :
    object.graph.Adj (shoulder port left) (shoulder port right) := by
  cases left <;> cases right
  · exact (different rfl).elim
  · exact TriangularShoulderCompletion.shoulder_adjacent_other setup
      (site port false)
  · exact TriangularShoulderCompletion.shoulder_adjacent_other setup
      (site port true)
  · exact (different rfl).elim

/-- Distinct triangular ports at a four-cycle-free high centre have
nonadjacent port endpoints. -/
theorem endpoint_nonadjacent
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (distinct : first ≠ second) :
    ¬object.graph.Adj
      (HighCenterPort.endpoint object center first.1)
      (HighCenterPort.endpoint object center second.1) := by
  intro endpointsAdjacent
  have endpointsNe : HighCenterPort.endpoint object center first.1 ≠
      HighCenterPort.endpoint object center second.1 := fun equal =>
    distinct (Subtype.ext (HighCenterPort.endpoint_injective object center equal))
  have firstNeCenter : HighCenterPort.endpoint object center first.1 ≠ center :=
    (HighCenterPort.endpoint_adjacent object center first.1).ne.symm
  have member := HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
    object center second.1 endpointsAdjacent.symm firstNeCenter
  rcases HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
      object center setup.centerHigh setup.deletionCritical second.1 member with
    firstEq | secondEq
  · apply setup.fourFree
    exact ⟨HighCenterStructure.squareCycle
      (HighCenterPort.endpoint_adjacent object center first.1)
      (by
        rw [firstEq]
        exact HighCenterPort.shoulders_adjacent_of_triangular object center
          setup.centerHigh setup.deletionCritical second.1 second.2)
      (HighCenterPort.secondShoulder_adjacent_endpoint object center
        setup.centerHigh setup.deletionCritical second.1)
      (HighCenterPort.endpoint_adjacent object center second.1).symm
      (TriangularShoulderCompletion.otherShoulder_ne_center setup
        (site second false)).symm endpointsNe⟩
  · apply setup.fourFree
    exact ⟨HighCenterStructure.squareCycle
      (HighCenterPort.endpoint_adjacent object center first.1)
      (by
        rw [secondEq]
        exact (HighCenterPort.shoulders_adjacent_of_triangular object center
          setup.centerHigh setup.deletionCritical second.1 second.2).symm)
      (HighCenterPort.firstShoulder_adjacent_endpoint object center
        setup.centerHigh setup.deletionCritical second.1)
      (HighCenterPort.endpoint_adjacent object center second.1).symm
      (TriangularShoulderCompletion.otherShoulder_ne_center setup
        (site second true)).symm endpointsNe⟩

/-- The two shoulder pairs of distinct triangular ports are disjoint. -/
theorem shoulder_pairs_disjoint
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (distinct : first ≠ second)
    (left right : Bool) :
    shoulder first left ≠ shoulder second right := by
  intro equal
  have endpointsNe : HighCenterPort.endpoint object center first.1 ≠
      HighCenterPort.endpoint object center second.1 := fun endpointEq =>
    distinct (Subtype.ext
      (HighCenterPort.endpoint_injective object center endpointEq))
  exact HighCenterStructure.nonadjacentNeighbors_noCommonOutside setup.fourFree
    endpointsNe (TriangularShoulderCompletion.shoulder_ne_center setup
      (site first left))
    (HighCenterPort.endpoint_adjacent object center first.1)
    (HighCenterPort.endpoint_adjacent object center second.1)
    (TriangularShoulderCompletion.shoulder_adjacent_endpoint setup
      (site first left)).symm
    (by
      change object.graph.Adj
        (HighCenterPort.endpoint object center second.1)
        (shoulder first left)
      rw [equal]
      exact (TriangularShoulderCompletion.shoulder_adjacent_endpoint setup
        (site second right)).symm)

def HighShoulder
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : Prop :=
  (∃ side : Bool, 4 ≤ object.degree (shoulder first side)) ∨
    ∃ side : Bool, 4 ≤ object.degree (shoulder second side)

private theorem high_left_of_shared
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (distinct : first ≠ second)
    (left right₁ right₂ : Bool) (rightNe : right₁ ≠ right₂)
    (edge₁ : object.graph.Adj (shoulder first left) (shoulder second right₁))
    (edge₂ : object.graph.Adj (shoulder first left) (shoulder second right₂)) :
    4 ≤ object.degree (shoulder first left) := by
  letI : DecidableEq V := object.input.vertices.decEq
  let ownEndpoint := HighCenterPort.endpoint object center first.1
  let ownOther := TriangularShoulderCompletion.otherShoulder setup
    (site first left)
  let cross₁ := shoulder second right₁
  let cross₂ := shoulder second right₂
  have endpointNeOther : ownEndpoint ≠ ownOther :=
    (TriangularShoulderCompletion.otherShoulder_adjacent_endpoint setup
      (site first left)).symm.ne
  have endpointNeCross₁ : ownEndpoint ≠ cross₁ := by
    intro equal
    exact endpoint_nonadjacent first second distinct
      (by
        change HighCenterPort.endpoint object center first.1 =
          shoulder second right₁ at equal
        rw [equal]
        exact TriangularShoulderCompletion.shoulder_adjacent_endpoint setup
          (site second right₁))
  have endpointNeCross₂ : ownEndpoint ≠ cross₂ := by
    intro equal
    exact endpoint_nonadjacent first second distinct
      (by
        change HighCenterPort.endpoint object center first.1 =
          shoulder second right₂ at equal
        rw [equal]
        exact TriangularShoulderCompletion.shoulder_adjacent_endpoint setup
          (site second right₂))
  have ownOtherEq : ownOther = shoulder first (!left) := by
    change TriangularShoulderCompletion.otherShoulder setup (site first left) =
      TriangularShoulderCompletion.shoulder setup (site first (!left))
    exact (TriangularShoulderCompletion.shoulder_oppositeSite setup
      (site first left)).symm
  have otherNeCross₁ : ownOther ≠ cross₁ := by
    rw [ownOtherEq]
    exact shoulder_pairs_disjoint first second distinct (!left) right₁
  have otherNeCross₂ : ownOther ≠ cross₂ := by
    rw [ownOtherEq]
    exact shoulder_pairs_disjoint first second distinct (!left) right₂
  have crossNe : cross₁ ≠ cross₂ := fun equal =>
    rightNe (shoulder_injective second equal)
  have fourCard : ({ownEndpoint, ownOther, cross₁, cross₂} : Finset V).card = 4 := by
    simp [endpointNeOther, endpointNeCross₁, endpointNeCross₂,
      otherNeCross₁, otherNeCross₂, crossNe]
  rw [← fourCard]
  apply object.card_le_degree_of_adjacent_finset (shoulder first left)
  intro vertex member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact TriangularShoulderCompletion.shoulder_adjacent_endpoint setup
      (site first left)
  · exact TriangularShoulderCompletion.shoulder_adjacent_other setup
      (site first left)
  · exact edge₁
  · exact edge₂

private theorem high_right_of_shared
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (distinct : first ≠ second)
    (left₁ left₂ right : Bool) (leftNe : left₁ ≠ left₂)
    (edge₁ : object.graph.Adj (shoulder first left₁) (shoulder second right))
    (edge₂ : object.graph.Adj (shoulder first left₂) (shoulder second right)) :
    4 ≤ object.degree (shoulder second right) := by
  exact high_left_of_shared second first distinct.symm right left₁ left₂ leftNe
    edge₁.symm edge₂.symm

/-- Two distinct cross edges force the high-shoulder branch; the alternative
vertex-disjoint configuration would be a forbidden four-cycle. -/
theorem highShoulder_of_two
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second)
    (edge₁ edge₂ : CrossEdge first second) (edgesNe : edge₁ ≠ edge₂) :
    HighShoulder first second := by
  by_cases leftEq : edge₁.1.1 = edge₂.1.1
  · left
    have rightNe : edge₁.1.2 ≠ edge₂.1.2 := by
      intro rightEq
      exact edgesNe (Subtype.ext (Prod.ext leftEq rightEq))
    have secondEdge : object.graph.Adj (shoulder first edge₁.1.1)
        (shoulder second edge₂.1.2) := by
      have raw := edge₂.2
      change object.graph.Adj (shoulder first edge₂.1.1)
        (shoulder second edge₂.1.2) at raw
      simpa [leftEq] using raw
    exact ⟨edge₁.1.1, high_left_of_shared first second portsNe
      edge₁.1.1 edge₁.1.2 edge₂.1.2 rightNe edge₁.2 secondEdge⟩
  by_cases rightEq : edge₁.1.2 = edge₂.1.2
  · right
    have secondEdge : object.graph.Adj (shoulder first edge₂.1.1)
        (shoulder second edge₁.1.2) := by
      have raw := edge₂.2
      change object.graph.Adj (shoulder first edge₂.1.1)
        (shoulder second edge₂.1.2) at raw
      simpa [rightEq] using raw
    exact ⟨edge₁.1.2, high_right_of_shared first second portsNe
      edge₁.1.1 edge₂.1.1 edge₁.1.2 leftEq edge₁.2 secondEdge⟩
  · apply (setup.fourFree ?_).elim
    exact ⟨HighCenterStructure.squareCycle edge₁.2
      (shoulder_adjacent_of_ne second rightEq)
      edge₂.2.symm
      (shoulder_adjacent_of_ne first leftEq).symm
      (shoulder_pairs_disjoint first second portsNe edge₁.1.1 edge₂.1.2)
      (shoulder_pairs_disjoint first second portsNe edge₂.1.1 edge₁.1.2).symm⟩

def capability
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : CT9.Capability base.problem where
  Item := CrossEdge first second
  Label := Unit
  labels := Core.Enumeration.unit
  label := fun _edge => ()
  capacity := fun _label => 1

def input
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : CT9.Input (capability first second) where
  context := ⟨object, baseline, ()⟩
  items := (crossEdges first second).toOrderedCollection

def run
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) :=
  CT9.run (capability first second) (input first second)

inductive Decision
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : Type where
  | high (witness : HighShoulder first second)
  | bounded (certificate : CT9.fibreCount (capability first second)
      (input first second) () ≤ 1)

def decision
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second) :
    Decision first second :=
  match run first second with
  | ⟨_, _, .overloaded residual⟩ =>
      let pair := residual.sameLabelPairOfCapacityOne rfl
      .high (highShoulder_of_two first second portsNe
        pair.first pair.second pair.distinct)
  | ⟨_, _, .bounded certificate⟩ =>
      .bounded (certificate.bounded ())

theorem stateSpace
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second) :
    HighShoulder first second ∨
      CT9.fibreCount (capability first second) (input first second) () ≤ 1 := by
  cases decision first second portsNe with
  | high witness => exact Or.inl witness
  | bounded certificate => exact Or.inr certificate

/-- Once every shoulder is cubic, the exact CT9 reference run is forced to
the bounded terminal. -/
def boundedRunOfCubic
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second)
    (cubic : (∀ side, object.degree (shoulder first side) = 3) ∧
      ∀ side, object.degree (shoulder second side) = 3) :
    CT9.BoundedRun (capability first second) (input first second) :=
  CT9.runBoundedOfBounded (capability first second) (input first second) <| by
    intro label
    rcases label with ⟨⟩
    rcases stateSpace first second portsNe with high | bounded
    · rcases high with ⟨side, high⟩ | ⟨side, high⟩
      · rw [cubic.1 side] at high
        omega
      · rw [cubic.2 side] at high
        omega
    · exact bounded

def checks
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : Nat :=
  (crossEdges first second).card + 1

theorem crossEdges_card_le_four
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : (crossEdges first second).card ≤ 4 := by
  letI : FinEnum Candidate := candidates
  letI : FinEnum (CrossEdge first second) := crossEdges first second
  have bound : Fintype.card (CrossEdge first second) ≤ Fintype.card Candidate :=
    Fintype.card_subtype_le _
  simpa [Candidate, FinEnum.card_eq_fintypeCard] using bound

theorem checks_constant
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) : checks first second ≤ 5 := by
  unfold checks
  have bound := crossEdges_card_le_four first second
  omega

structure VerifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second) : Prop where
  traceValid : CT9.Graph.ValidTrace (capability first second)
    (input first second) (run first second).trace
  total : (run first second).terminal = .overloaded ∨
    (run first second).terminal = .bounded
  stateSpace : HighShoulder first second ∨
    CT9.fibreCount (capability first second) (input first second) () ≤ 1
  polynomial : checks first second ≤ 5

def verifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (first second : TriPort setup) (portsNe : first ≠ second) :
    VerifiedStage first second portsNe where
  traceValid := CT9.run_trace_valid _ _
  total := CT9.outcome_exhaustive _ _ _
  stateSpace := stateSpace first second portsNe
  polynomial := checks_constant first second

end StructuralExhaustion.Graph.TriangularCrossShoulder
