import Mathlib.Tactic
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Graph.TriangularPortReturn

namespace StructuralExhaustion.Graph.TriangularFirstLanding

open StructuralExhaustion

universe u

/-!
# Exact first-landings at triangular shoulders

The finite data are the literal shoulder-completion incidences in one
triangular fan.  CT10 classifies that explicit table into the three manuscript
landing kinds.  The semantic theorem is graph-local: four-cycle freeness rules
out every noncentral neighbour of the fan centre, while the definition of a
completion incidence rules out the two shoulders of its own port.

Only the declared port, shoulder, and vertex enumerations are inspected.  No
path, subgraph, graph, or ambient context universe is generated.
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

abbrev Site
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  TriangularShoulderCompletion.Site setup

abbrev Candidate
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  Site setup × V

/-- One actual completion incidence, not merely a candidate endpoint. -/
abbrev Incidence
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  {candidate : Candidate setup //
    TriangularShoulderCompletion.IsCompletion setup candidate.1 candidate.2}

@[implicit_reducible]
def candidates
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    FinEnum (Candidate setup) :=
  Core.Enumeration.prod (TriangularShoulderCompletion.sites setup)
    object.input.vertices

@[implicit_reducible]
def incidences
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    FinEnum (Incidence setup) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidableEq V := object.input.vertices.decEq
  exact Core.Enumeration.subtype (candidates setup)
    (fun candidate => TriangularShoulderCompletion.IsCompletion setup
      candidate.1 candidate.2)
    (fun _candidate => by
      unfold TriangularShoulderCompletion.IsCompletion
      infer_instance)

inductive LandingClass where
  | central
  | crossTriangular
  | outside
  deriving Repr, DecidableEq

@[implicit_reducible]
def landingClasses : FinEnum LandingClass :=
  FinEnum.ofNodupList [.central, .crossTriangular, .outside]
    (by intro cls; cases cls <;> simp) (by decide)

def Central
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) : Prop :=
  incidence.1.2 = center

def CrossTriangular
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) : Prop :=
  ∃ other : Site setup, other.1 ≠ incidence.1.1.1 ∧
    incidence.1.2 = TriangularShoulderCompletion.shoulder setup other

/-- Membership in the displayed triangular fan core. -/
def FanCoreVertex
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) (vertex : V) : Prop :=
  vertex = center ∨
    (∃ port : TriPort setup,
      vertex = HighCenterPort.endpoint object center port.1) ∨
    ∃ site : Site setup,
      vertex = TriangularShoulderCompletion.shoulder setup site

def Outside
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) : Prop :=
  ¬FanCoreVertex setup incidence.1.2 ∧
    ¬object.graph.Adj center incidence.1.2

private theorem samePort_shoulder_eq
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center)
    (site other : Site setup) (same : other.1 = site.1) :
    TriangularShoulderCompletion.shoulder setup other =
        TriangularShoulderCompletion.shoulder setup site ∨
      TriangularShoulderCompletion.shoulder setup other =
        TriangularShoulderCompletion.otherShoulder setup site := by
  rcases site with ⟨port, side⟩
  rcases other with ⟨otherPort, otherSide⟩
  change otherPort = port at same
  subst otherPort
  cases side <;> cases otherSide
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Completion incidences cannot land at any port vertex of the fan. -/
theorem endpoint_ne_portVertex
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) (port : TriPort setup) :
    incidence.1.2 ≠ HighCenterPort.endpoint object center port.1 := by
  intro endpointEq
  have centerAdjacent : object.graph.Adj center incidence.1.2 := by
    rw [endpointEq]
    exact HighCenterPort.endpoint_adjacent object center port.1
  have endpointNeCenter : incidence.1.2 ≠ center := by
    rw [endpointEq]
    exact (HighCenterPort.endpoint_adjacent object center port.1).ne.symm
  exact TriangularShoulderCompletion.completion_not_other_center_neighbor
    setup incidence.1.1 incidence.2 centerAdjacent endpointNeCenter

/-- The three manuscript landing predicates are disjoint and exhaustive. -/
theorem landing_exhaustive
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) :
    Central incidence ∨ CrossTriangular incidence ∨ Outside incidence := by
  classical
  by_cases central : incidence.1.2 = center
  · exact Or.inl central
  by_cases cross : CrossTriangular incidence
  · exact Or.inr (Or.inl cross)
  right; right
  refine ⟨?_, ?_⟩
  · intro coreMember
    rcases coreMember with centerEq | portVertex | shoulderVertex
    · exact central centerEq
    · rcases portVertex with ⟨port, equal⟩
      exact endpoint_ne_portVertex incidence port equal
    · rcases shoulderVertex with ⟨other, equal⟩
      by_cases samePort : other.1 = incidence.1.1.1
      · rcases samePort_shoulder_eq setup incidence.1.1 other samePort with
          sameShoulder | otherShoulder
        · exact incidence.2.1.ne (equal.trans sameShoulder).symm
        · exact incidence.2.2.2 (equal.trans otherShoulder)
      · exact cross ⟨other, samePort, equal⟩
  · intro centerAdjacent
    exact TriangularShoulderCompletion.completion_not_other_center_neighbor
      setup incidence.1.1 incidence.2 centerAdjacent central

/-- Executable three-way class of one actual completion incidence. -/
def classOf
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) : LandingClass := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : FinEnum (TriPort setup) :=
    HighCenterPort.triangularPorts object center setup.centerHigh
      setup.deletionCritical
  letI : DecidableEq (TriPort setup) :=
    (HighCenterPort.triangularPorts object center setup.centerHigh
      setup.deletionCritical).decEq
  letI : FinEnum (Site setup) :=
    TriangularShoulderCompletion.sites setup
  letI : Decidable (Central incidence) := by
    unfold Central
    infer_instance
  letI : Decidable (CrossTriangular incidence) := by
    unfold CrossTriangular
    infer_instance
  exact if Central incidence then .central
    else if CrossTriangular incidence then .crossTriangular else .outside

/-- The computed class is definitionally faithful to the mathematical
landing predicates. -/
theorem classOf_sound
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) :
    match classOf incidence with
    | .central => Central incidence
    | .crossTriangular => CrossTriangular incidence
    | .outside => Outside incidence := by
  classical
  unfold classOf
  by_cases central : Central incidence
  · simp [central]
  by_cases cross : CrossTriangular incidence
  · simp [central, cross]
  simp only [central, cross, ↓reduceIte]
  rcases landing_exhaustive incidence with central' | cross' | outside
  · exact (central central').elim
  · exact (cross cross').elim
  · exact outside

def capability
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT10.Capability base.problem where
  Datum := Incidence setup
  Class := LandingClass
  Promotion := LandingClass
  classes := landingClasses
  classOf := classOf
  Direct := fun _ => False
  directDecidable := fun _ => isFalse id
  promote := id

def input
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT10.Input (capability setup) where
  context := ⟨object, baseline, ()⟩
  data := (incidences setup).toOrderedCollection

def run
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :=
  CT10.run (capability setup) (input setup)

theorem run_traceValid
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    CT10.Graph.ValidTrace (capability setup) (input setup)
      (run setup).trace := by
  exact CT10.run_trace_valid (capability setup) (input setup)

theorem run_terminal_total
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (run setup).terminal = .direct ∨
      (run setup).terminal = .promoted ∨
      (run setup).terminal = .exhaustive :=
  CT10.outcome_exhaustive (capability setup) (input setup) (run setup)

theorem run_total
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    ∃ result, result = run setup ∧
      (result.terminal = .direct ∨ result.terminal = .promoted ∨
        result.terminal = .exhaustive) ∧
      CT10.Graph.ValidTrace (capability setup) (input setup) result.trace :=
  ⟨run setup, rfl, run_terminal_total setup, run_traceValid setup⟩

theorem stateSpace
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (∃ cls : LandingClass,
        CT10.row (capability setup) (input setup) cls = []) ∨
      (∀ cls : LandingClass, ∃ incidence : Incidence setup,
        incidence ∈ CT10.row (capability setup) (input setup) cls) := by
  generalize resultEquation : run setup = result
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | direct residual => exact residual.direct.elim
      | promoted residual =>
          exact .inl ⟨residual.missing.cls, residual.missing.empty⟩
      | exhaustive certificate =>
          exact .inr certificate.populated

def checks
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) : Nat :=
  3 * (incidences setup).card + 3

theorem incidence_card_le_twice_square
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    (incidences setup).card ≤ 2 * object.input.vertices.card ^ 2 := by
  letI : FinEnum V := object.input.vertices
  letI : FinEnum (Site setup) :=
    TriangularShoulderCompletion.sites setup
  letI : FinEnum (Candidate setup) := candidates setup
  letI : FinEnum (Incidence setup) := incidences setup
  have subtypeLe : Fintype.card (Incidence setup) ≤
      Fintype.card (Candidate setup) :=
    Fintype.card_subtype_le _
  have sitesLe :=
    TriangularShoulderCompletion.sites_card_le_twice_vertices setup
  have candidateCard : Fintype.card (Candidate setup) =
      (TriangularShoulderCompletion.sites setup).card *
        object.input.vertices.card := by
    simp only [Candidate, Fintype.card_prod, FinEnum.card_eq_fintypeCard]
  calc
    (incidences setup).card = Fintype.card (Incidence setup) :=
      FinEnum.card_eq_fintypeCard
    _ ≤ Fintype.card (Candidate setup) := subtypeLe
    _ = (TriangularShoulderCompletion.sites setup).card *
        object.input.vertices.card := candidateCard
    _ ≤ (2 * object.input.vertices.card) *
        object.input.vertices.card :=
      Nat.mul_le_mul_right object.input.vertices.card sitesLe
    _ = 2 * object.input.vertices.card ^ 2 := by ring

theorem checks_quadratic
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    checks setup ≤ 6 * object.input.vertices.card ^ 2 + 3 := by
  unfold checks
  have incidenceLe := incidence_card_le_twice_square setup
  omega

/-- Complete framework-owned CT10 execution and semantic first-landing
classification for one triangular fan. -/
structure VerifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) : Prop where
  traceValid : CT10.Graph.ValidTrace (capability setup) (input setup)
    (run setup).trace
  total : ∃ result, result = run setup ∧
    (result.terminal = .direct ∨ result.terminal = .promoted ∨
      result.terminal = .exhaustive) ∧
    CT10.Graph.ValidTrace (capability setup) (input setup) result.trace
  stateSpace :
    (∃ cls : LandingClass,
        CT10.row (capability setup) (input setup) cls = []) ∨
      (∀ cls : LandingClass, ∃ incidence : Incidence setup,
        incidence ∈ CT10.row (capability setup) (input setup) cls)
  classifies : ∀ incidence : Incidence setup,
    match classOf incidence with
    | .central => Central incidence
    | .crossTriangular => CrossTriangular incidence
    | .outside => Outside incidence
  noPortVertex : ∀ (incidence : Incidence setup) (port : TriPort setup),
    incidence.1.2 ≠ HighCenterPort.endpoint object center port.1
  polynomial : checks setup ≤ 6 * object.input.vertices.card ^ 2 + 3

noncomputable def verifiedStage
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} (setup : Setup base object baseline center) :
    VerifiedStage setup where
  traceValid := run_traceValid setup
  total := run_total setup
  stateSpace := stateSpace setup
  classifies := classOf_sound
  noPortVertex := endpoint_ne_portVertex
  polynomial := checks_quadratic setup

/-! ## Framework-owned CT1-return to CT10-classification composition -/

def Classified
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    (incidence : Incidence setup) : Prop :=
  match classOf incidence with
  | .central => Central incidence
  | .crossTriangular => CrossTriangular incidence
  | .outside => Outside incidence

/-- The return's first relevant completion, whether it occurs at the initial
shoulder or after crossing the shoulder edge, is an actual datum of the CT10
table and carries its verified semantic landing class. -/
def ClassifiedReturnAlternative
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    {port : TriPort setup}
    (certificate : TriangularPortReturn.Certificate setup port) : Prop :=
  let Q := certificate.path
  let other := TriangularShoulderCompletion.otherShoulder setup certificate.site
  (Q.snd = center ∧ Q.length = 1) ∨
  (∃ incidence : Incidence setup,
    incidence.1 = (certificate.site, Q.snd) ∧ Classified incidence) ∨
  (Q.snd = other ∧ Q.tail.snd = center ∧ Q.length = 2) ∨
  ∃ incidence : Incidence setup,
    incidence.1 =
      (TriangularShoulderCompletion.oppositeSite setup certificate.site,
        Q.tail.snd) ∧
      Classified incidence

/-- Ordinary theorem composition between the framework-owned CT1 return and
the CT10 landing audit.  This is not a registered residual route: both stages
remain visible with their original typed results. -/
theorem classifyReturn
    {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
    {object : FiniteObject V} {baseline : base.problem.Baseline object}
    {center : V} {setup : Setup base object baseline center}
    {port : TriPort setup}
    {root : DartReturn object.graph (TriangularPortReturn.rootDart setup port)}
    {avoids : ¬HasCycleWithLength object.graph base.LengthOK}
    (returnStage : TriangularPortReturn.VerifiedStage setup port root avoids)
    (landingStage : VerifiedStage setup) :
    ClassifiedReturnAlternative
      (TriangularPortReturn.certificate setup port root) := by
  let certificate := TriangularPortReturn.certificate setup port root
  change ClassifiedReturnAlternative certificate
  rcases returnStage.landing with direct | firstCompletion |
      otherCentral | otherCompletion
  · exact Or.inl direct
  · rcases firstCompletion with ⟨_noncentral, _notOther, completion⟩
    let incidence : Incidence setup :=
      ⟨(certificate.site, certificate.path.snd), completion⟩
    exact Or.inr (Or.inl
      ⟨incidence, rfl, landingStage.classifies incidence⟩)
  · exact Or.inr (Or.inr (Or.inl otherCentral))
  · rcases otherCompletion with ⟨_firstOther, _noncentral, completion⟩
    let incidence : Incidence setup :=
      ⟨(TriangularShoulderCompletion.oppositeSite setup certificate.site,
        certificate.path.tail.snd), completion⟩
    exact Or.inr (Or.inr (Or.inr
      ⟨incidence, rfl, landingStage.classifies incidence⟩))

end StructuralExhaustion.Graph.TriangularFirstLanding
