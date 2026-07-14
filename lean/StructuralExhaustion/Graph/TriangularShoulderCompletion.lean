import Mathlib.Tactic
import StructuralExhaustion.CT5.Automation
import StructuralExhaustion.Graph.HighCenterPort

namespace StructuralExhaustion.Graph.TriangularShoulderCompletion

open StructuralExhaustion

universe u

/-!
# CT5 triangular-shoulder completion profile

For one high centre, the sites are exactly the two shoulders of every actual
triangular incident port.  A site's witnesses are the declared vertices, and
support means a literal completion edge different from the two triangle
edges.  CT5 chooses the first supporting endpoint in the declared order.
No path, subset, port pair, or graph universe is materialized.
-/

structure Setup
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) : Prop where
  centerHigh : 4 ≤ object.degree center
  threeLeMinimum : 3 ≤ base.minimumDegree
  deletionCritical : ∀ dart : object.graph.Dart,
    object.degree dart.fst = 3 ∨ object.degree dart.snd = 3
  fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength

abbrev TriPort
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  HighCenterPort.TriangularPort object center setup.centerHigh
    setup.deletionCritical

/-- One of the two shoulders of one triangular port. -/
abbrev Site
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  TriPort setup × Bool

@[implicit_reducible]
def sites
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    FinEnum (Site setup) :=
  Core.Enumeration.prod
    (HighCenterPort.triangularPorts object center setup.centerHigh
      setup.deletionCritical)
    Core.Enumeration.bool

def shoulder
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : V :=
  if site.2 then
    HighCenterPort.secondShoulder object center setup.centerHigh
      setup.deletionCritical site.1.1
  else
    HighCenterPort.firstShoulder object center setup.centerHigh
      setup.deletionCritical site.1.1

def otherShoulder
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : V :=
  if site.2 then
    HighCenterPort.firstShoulder object center setup.centerHigh
      setup.deletionCritical site.1.1
  else
    HighCenterPort.secondShoulder object center setup.centerHigh
      setup.deletionCritical site.1.1

/-- The other site of the same triangular port. -/
def oppositeSite
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : Site setup :=
  ⟨site.1, !site.2⟩

@[simp] theorem oppositeSite_port
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : (oppositeSite setup site).1 = site.1 := rfl

@[simp] theorem shoulder_oppositeSite
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    shoulder setup (oppositeSite setup site) = otherShoulder setup site := by
  rcases site with ⟨port, side⟩
  cases side <;> rfl

@[simp] theorem otherShoulder_oppositeSite
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    otherShoulder setup (oppositeSite setup site) = shoulder setup site := by
  rcases site with ⟨port, side⟩
  cases side <;> rfl

def endpoint
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : V :=
  HighCenterPort.endpoint object center site.1.1

/-- A literal shoulder-completion incidence: an edge different from the two
triangle edges at this shoulder. -/
def IsCompletion
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) (vertex : V) : Prop :=
  object.graph.Adj (shoulder setup site) vertex ∧
    vertex ≠ endpoint setup site ∧ vertex ≠ otherShoulder setup site

theorem shoulder_ne_other
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : shoulder setup site ≠ otherShoulder setup site := by
  rcases site with ⟨port, side⟩
  have distinct := HighCenterPort.firstShoulder_ne_secondShoulder object center
    setup.centerHigh setup.deletionCritical port.1
  cases side
  · simpa [shoulder, otherShoulder] using distinct
  · simpa [shoulder, otherShoulder] using distinct.symm

theorem shoulder_adjacent_endpoint
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    object.graph.Adj (shoulder setup site) (endpoint setup site) := by
  rcases site with ⟨port, side⟩
  cases side <;> simp [shoulder, endpoint,
    HighCenterPort.firstShoulder_adjacent_endpoint object center
      setup.centerHigh setup.deletionCritical port.1,
    HighCenterPort.secondShoulder_adjacent_endpoint object center
      setup.centerHigh setup.deletionCritical port.1]

theorem otherShoulder_adjacent_endpoint
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    object.graph.Adj (otherShoulder setup site) (endpoint setup site) := by
  rcases site with ⟨port, side⟩
  cases side <;> simp [otherShoulder, endpoint,
    HighCenterPort.firstShoulder_adjacent_endpoint object center
      setup.centerHigh setup.deletionCritical port.1,
    HighCenterPort.secondShoulder_adjacent_endpoint object center
      setup.centerHigh setup.deletionCritical port.1]

theorem shoulder_adjacent_other
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    object.graph.Adj (shoulder setup site) (otherShoulder setup site) := by
  rcases site with ⟨port, side⟩
  have adjacent := HighCenterPort.shoulders_adjacent_of_triangular object center
    setup.centerHigh setup.deletionCritical port.1 port.2
  cases side
  · simpa [shoulder, otherShoulder] using adjacent
  · simpa [shoulder, otherShoulder] using adjacent.symm

theorem shoulder_ne_center
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : shoulder setup site ≠ center := by
  rcases site with ⟨port, side⟩
  cases side
  · apply HighCenterPort.ne_center_of_mem_shoulders object center port.1
    exact HighCenterPort.firstShoulder_mem object center setup.centerHigh
      setup.deletionCritical port.1
  · apply HighCenterPort.ne_center_of_mem_shoulders object center port.1
    exact HighCenterPort.secondShoulder_mem object center setup.centerHigh
      setup.deletionCritical port.1

theorem otherShoulder_ne_center
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : otherShoulder setup site ≠ center := by
  rcases site with ⟨port, side⟩
  cases side
  · apply HighCenterPort.ne_center_of_mem_shoulders object center port.1
    exact HighCenterPort.secondShoulder_mem object center setup.centerHigh
      setup.deletionCritical port.1
  · apply HighCenterPort.ne_center_of_mem_shoulders object center port.1
    exact HighCenterPort.firstShoulder_mem object center setup.centerHigh
      setup.deletionCritical port.1

theorem shoulder_degree_atLeastThree
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : 3 ≤ object.degree (shoulder setup site) :=
  setup.threeLeMinimum.trans
    (baseline.trans (object.minDegree_le_degree (shoulder setup site)))

/-- Minimum degree supplies at least one completion endpoint at every site. -/
theorem exists_completion
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) : ∃ vertex, IsCompletion setup site vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableEq V := object.input.vertices.decEq
  by_contra absent
  have subset : object.graph.neighborFinset (shoulder setup site) ⊆
      {endpoint setup site, otherShoulder setup site} := by
    intro vertex member
    have adjacent : object.graph.Adj (shoulder setup site) vertex := by
      simpa [SimpleGraph.mem_neighborFinset] using member
    by_cases endpointEq : vertex = endpoint setup site
    · simp [endpointEq]
    by_cases otherEq : vertex = otherShoulder setup site
    · simp [otherEq]
    exact (absent ⟨vertex, adjacent, endpointEq, otherEq⟩).elim
  have cardLe := Finset.card_le_card subset
  have pairCard : ({endpoint setup site, otherShoulder setup site} : Finset V).card = 2 := by
    simp [(otherShoulder_adjacent_endpoint setup site).symm.ne]
  have neighborCard :
      (object.graph.neighborFinset (shoulder setup site)).card =
        object.degree (shoulder setup site) := by
    rfl
  have upper : object.degree (shoulder setup site) ≤ 2 := by
    rw [← neighborCard, ← pairCard]
    exact cardLe
  exact (Nat.not_succ_le_self 2)
    ((shoulder_degree_atLeastThree setup site).trans upper)

/-- The two shoulders cannot both be neighbours of the centre. -/
theorem not_both_shoulders_central
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (port : TriPort setup) :
    ¬(object.graph.Adj center
        (HighCenterPort.firstShoulder object center setup.centerHigh
          setup.deletionCritical port.1) ∧
      object.graph.Adj center
        (HighCenterPort.secondShoulder object center setup.centerHigh
          setup.deletionCritical port.1)) := by
  rintro ⟨centerFirst, centerSecond⟩
  have endpointEq := HighCenterStructure.neighborhood_isMatching setup.fourFree
    (HighCenterPort.endpoint_adjacent object center port.1)
    centerFirst centerSecond
    (HighCenterPort.firstShoulder_adjacent_endpoint object center
      setup.centerHigh setup.deletionCritical port.1).symm
    (HighCenterPort.shoulders_adjacent_of_triangular object center
      setup.centerHigh setup.deletionCritical port.1 port.2)
  exact (HighCenterPort.secondShoulder_adjacent_endpoint object center
    setup.centerHigh setup.deletionCritical port.1).ne endpointEq.symm

/-- A central shoulder is cubic by deletion criticality. -/
theorem central_shoulder_cubic
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup)
    (central : object.graph.Adj center (shoulder setup site)) :
    object.degree (shoulder setup site) = 3 := by
  have critical := setup.deletionCritical
    ⟨(center, shoulder setup site), central⟩
  change object.degree center = 3 ∨ object.degree (shoulder setup site) = 3
    at critical
  rcases critical with centerCubic | shoulderCubic
  · have centerHigh := setup.centerHigh
    omega
  · exact shoulderCubic

/-- At a central shoulder, every completion incidence is the central edge. -/
theorem completion_eq_center_of_central
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) {vertex : V}
    (central : object.graph.Adj center (shoulder setup site))
    (completion : IsCompletion setup site vertex) : vertex = center := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableEq V := object.input.vertices.decEq
  by_contra vertexNeCenter
  let x := endpoint setup site
  let other := otherShoulder setup site
  have xNeOther : x ≠ other :=
    (otherShoulder_adjacent_endpoint setup site).symm.ne
  have xNeCenter : x ≠ center :=
    (HighCenterPort.endpoint_adjacent object center site.1.1).ne.symm
  have xNeVertex : x ≠ vertex := Ne.symm completion.2.1
  have otherNeCenter : other ≠ center := otherShoulder_ne_center setup site
  have otherNeVertex : other ≠ vertex := Ne.symm completion.2.2
  have centerNeVertex : center ≠ vertex := Ne.symm vertexNeCenter
  have fourCard : ({x, other, center, vertex} : Finset V).card = 4 := by
    simp [xNeOther, xNeCenter, xNeVertex, otherNeCenter,
      otherNeVertex, centerNeVertex]
  have subset : ({x, other, center, vertex} : Finset V) ⊆
      object.graph.neighborFinset (shoulder setup site) := by
    intro value member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa [x] using shoulder_adjacent_endpoint setup site
    · simpa [other] using shoulder_adjacent_other setup site
    · simpa [SimpleGraph.mem_neighborFinset] using central.symm
    · simpa [SimpleGraph.mem_neighborFinset] using completion.1
  have cardLe := Finset.card_le_card subset
  have neighborCard :
      (object.graph.neighborFinset (shoulder setup site)).card = 3 := by
    change object.degree (shoulder setup site) = 3
    exact central_shoulder_cubic setup site central
  rw [fourCard, neighborCard] at cardLe
  omega

/-- No completion endpoint can be a noncentral neighbour of the high centre. -/
theorem completion_not_other_center_neighbor
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) {vertex : V}
    (completion : IsCompletion setup site vertex)
    (centerAdjacent : object.graph.Adj center vertex)
    (_vertexNeCenter : vertex ≠ center) : False := by
  apply setup.fourFree
  exact ⟨HighCenterStructure.squareCycle
    (HighCenterPort.endpoint_adjacent object center site.1.1)
    (shoulder_adjacent_endpoint setup site).symm
    completion.1 centerAdjacent.symm
    (Ne.symm (shoulder_ne_center setup site))
    (Ne.symm completion.2.1)⟩

/-! ## Exact CT5 witness ledger -/

def spec
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT5.Spec base.problem where
  Site := Site setup
  Witness := fun _site => V
  Active := fun _ctx _site => True
  Supports := fun _ctx site vertex => IsCompletion setup site vertex
  contribution := fun _ctx _site _vertex => 1

def capability
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT5.Capability (spec setup) where
  sites := sites setup
  witnesses := fun _site => object.input.vertices
  activeDecidable := fun _ctx _site => isTrue trivial
  supportsDecidable := by
    intro _ctx site vertex
    letI : DecidableRel object.graph.Adj := object.input.decideAdj
    letI : DecidableEq V := object.input.vertices.decEq
    change Decidable (IsCompletion setup site vertex)
    unfold IsCompletion
    infer_instance
  required := fun _ctx => 0
  capacity := fun _ctx => (sites setup).card

def context
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    CT5.Input base.problem := ⟨object, baseline, ()⟩

def run
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  CT5.run (spec setup) (capability setup) (context base object baseline)

theorem noDeficit
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    ∀ site, ¬CT5.DeficitAt (spec setup) (context base object baseline) site := by
  intro site deficit
  obtain ⟨vertex, completion⟩ := exists_completion setup site
  exact deficit.2 vertex completion

theorem contributionAt_eq_one
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site : Site setup) :
    CT5.contributionAt (spec setup) (capability setup)
      (context base object baseline) site = 1 := by
  unfold CT5.contributionAt
  simp only [capability]
  split
  · rename_i witness supported
    rfl
  · rename_i absent searchAbsent
    obtain ⟨vertex, completion⟩ := exists_completion setup site
    exact (absent vertex completion).elim

theorem ledgerTotal_eq_sites
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT5.ledgerTotal (spec setup) (capability setup)
      (context base object baseline) = (sites setup).card := by
  unfold CT5.ledgerTotal
  simp_rw [contributionAt_eq_one setup]
  have foldOne : ∀ (values : List (Site setup)) (initial : Nat),
      values.foldl (fun total _site => total + 1) initial =
        initial + values.length := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons head tail ih =>
        intro initial
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  change (sites setup).orderedValues.foldl
      (fun total _site => total + 1) 0 = (sites setup).card
  rw [foldOne]
  simp [FinEnum.orderedValues, FinEnum.toList]

theorem analyzeDeficit_clear
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    ∃ state, CT5.analyzeDeficit (spec setup) (capability setup)
      (context base object baseline) = .clear state := by
  cases equation : CT5.analyzeDeficit (spec setup) (capability setup)
      (context base object baseline) with
  | deficit residual =>
      exact (noDeficit setup residual.site
        ⟨residual.active, residual.noWitness⟩).elim
  | clear state => exact ⟨state, rfl⟩

theorem compare_charge
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (state : CT5.DeficitFreeState (spec setup) (capability setup)
      (context base object baseline)) :
    ∃ residual, CT5.compare (spec setup) (capability setup)
      (context base object baseline)
      (CT5.computeLedger (spec setup) (capability setup)
        (context base object baseline) state) = .charge residual := by
  cases equation : CT5.compare (spec setup) (capability setup)
      (context base object baseline)
      (CT5.computeLedger (spec setup) (capability setup)
        (context base object baseline) state) with
  | closes certificate =>
      have impossible : (sites setup).card < 0 := by
        simpa [capability, context] using certificate.capacity_lt_required
      omega
  | charge residual => exact ⟨residual, rfl⟩
  | aggregate residual =>
      have totalEq : residual.ledger.total = (sites setup).card := by
        rw [residual.ledger.computed]
        exact ledgerTotal_eq_sites setup
      have tooLarge : (sites setup).card < residual.ledger.total := by
        simpa [capability, context] using residual.capacity_lt_total
      omega

theorem run_terminal_charge
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (run setup).terminal = .charge := by
  obtain ⟨state, clear⟩ := analyzeDeficit_clear setup
  obtain ⟨residual, compared⟩ := compare_charge setup state
  simp [run, CT5.run, CT5.runReference, clear, compared]

theorem run_trace_charge
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (run setup).trace =
      [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal] := by
  have terminal := run_terminal_charge setup
  generalize resultEquation : run setup = result at terminal ⊢
  cases result with
  | mk resultTerminal path outcome =>
      dsimp only at terminal
      subst resultTerminal
      exact CT5.Graph.trace_eq_of_path_to_charge _ _ _ path

def checks
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) : Nat :=
  (sites setup).card * object.input.vertices.card + (sites setup).card + 2

theorem sites_card_le_twice_vertices
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (sites setup).card ≤ 2 * object.input.vertices.card := by
  have triangularLe := HighCenterPort.triangularPorts_card_le_ports object center
    setup.centerHigh setup.deletionCritical
  have portsEq := HighCenterPort.ports_card_eq_degree object center
  have degreeLe := HighCenterPort.degree_le_vertexCount object center
  have siteEq : (sites setup).card =
      2 * (HighCenterPort.triangularPorts object center setup.centerHigh
        setup.deletionCritical).card := by
    simp [FinEnum.card_eq_fintypeCard, Nat.mul_comm]
  rw [siteEq]
  omega

theorem checks_quadratic
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    checks setup ≤ 2 * object.input.vertices.card ^ 2 +
      2 * object.input.vertices.card + 2 := by
  unfold checks
  have siteLe := sites_card_le_twice_vertices setup
  nlinarith

structure Bookkeeping
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) : Prop where
  completion : ∀ site : Site setup, ∃ vertex, IsCompletion setup site vertex
  atMostOneCentral : ∀ port : TriPort setup, ¬(
    object.graph.Adj center
      (HighCenterPort.firstShoulder object center setup.centerHigh
        setup.deletionCritical port.1) ∧
    object.graph.Adj center
      (HighCenterPort.secondShoulder object center setup.centerHigh
        setup.deletionCritical port.1))
  centralCubic : ∀ site : Site setup,
    object.graph.Adj center (shoulder setup site) →
      object.degree (shoulder setup site) = 3
  centralUnique : ∀ (site : Site setup) (vertex : V),
    object.graph.Adj center (shoulder setup site) →
      IsCompletion setup site vertex → vertex = center
  noOtherCenterEndpoint : ∀ (site : Site setup) (vertex : V),
    IsCompletion setup site vertex → object.graph.Adj center vertex →
      vertex ≠ center → False

structure VerifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) : Prop where
  terminal : (run setup).terminal = .charge
  trace : (run setup).trace =
    [.entry, .deficitSearch, .summation, .comparison, .chargeTerminal]
  ledgerTotal : CT5.ledgerTotal (spec setup) (capability setup)
    (context base object baseline) = (sites setup).card
  bookkeeping : Bookkeeping setup
  total : ∃ result : CT5.ExecutionResult (spec setup) (capability setup)
      (context base object baseline),
    result.outcome.Valid ∧ CT5.Graph.ValidTrace (spec setup)
      (capability setup) (context base object baseline) result.trace
  polynomial : checks setup ≤ 2 * object.input.vertices.card ^ 2 +
    2 * object.input.vertices.card + 2

def verifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    VerifiedStage setup where
  terminal := run_terminal_charge setup
  trace := run_trace_charge setup
  ledgerTotal := ledgerTotal_eq_sites setup
  bookkeeping := {
    completion := exists_completion setup
    atMostOneCentral := not_both_shoulders_central setup
    centralCubic := central_shoulder_cubic setup
    centralUnique := completion_eq_center_of_central setup
    noOtherCenterEndpoint := completion_not_other_center_neighbor setup
  }
  total := CT5.run_total (spec setup) (capability setup)
    (context base object baseline)
  polynomial := checks_quadratic setup

end StructuralExhaustion.Graph.TriangularShoulderCompletion
