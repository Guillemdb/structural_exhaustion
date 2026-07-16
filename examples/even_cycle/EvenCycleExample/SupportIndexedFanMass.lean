import EvenCycleExample.Concrete
import StructuralExhaustion.Graph.SupportIndexedFanMass

namespace EvenCycleExample.SupportIndexedFanMass

open StructuralExhaustion

/-!
An independent graph-semantic transfer of the support-indexed CT14 profile.
The members are the four actual vertex-centred fan supports of the concrete
`K₄`; the centers and occurrences are the same four concrete vertices.  Thus
the execution scans only the displayed local support and occurrence schedules.
-/

abbrev Support := ConcreteK4.Vertex
abbrev Center := ConcreteK4.Vertex
abbrev Occurrence := ConcreteK4.Vertex

/-- The literal fan support at a concrete `K₄` vertex. -/
def fanSupport (support : Support) : Finset ConcreteK4.Vertex :=
  (ConcreteK4.object.input.orderedNeighbors support).toFinset

theorem fanSupport_card (support : Support) :
    (fanSupport support).card = 3 := by
  cases support <;> native_decide

def role : Support → Graph.SupportIndexedFanMass.Role
  | .v0 | .v1 => .ordinary
  | .v2 | .v3 => .grouped

/-- Each fan support carries the surplus token at its own center. -/
def occurrenceSupport (occurrence : Occurrence) : Support := occurrence

def occurrenceCenter (occurrence : Occurrence) : Center := occurrence

def centerSurplus (center : Center) : Nat :=
  ConcreteK4.object.degree center - 2

def deficit (support : Support) : Nat :=
  ConcreteK4.object.degree support - 2

def profile : Graph.SupportIndexedFanMass.Profile Support Center Occurrence where
  supports := ConcreteK4.vertices
  centers := ConcreteK4.vertices
  occurrences := ConcreteK4.vertices
  role := role
  occurrenceSupport := occurrenceSupport
  occurrenceCenter := occurrenceCenter
  supportDecidableEq := inferInstance
  centerSurplus := centerSurplus
  deficit := deficit
  extracted := fun _ => False
  extractedDecidable := fun _ => inferInstance
  coefficient := 1
  localBound := by
    intro support _notExtracted
    cases support <;> native_decide
  withinRoleDisjoint := by
    intro left right equal
    exact congrArg Prod.snd equal

def context : Core.BranchContext ConcreteK4.surplusBase.problem :=
  Graph.FanClosedPortMass.context ConcreteK4.surplusBase ConcreteK4.object
    ConcreteK4.minimumDegreeThree

def stage : profile.VerifiedStage context :=
  profile.verifiedStage context

theorem terminal : (profile.run context).terminal = .capacity :=
  stage.terminal

theorem trace : (profile.run context).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal] :=
  stage.trace

theorem validity : (profile.run context).outcome.Valid :=
  stage.verified

theorem traceValidity : @CT14.Graph.ValidTrace
    ConcreteK4.surplusBase.problem
    (profile.capability ConcreteK4.surplusBase.problem) context
    (profile.run context).trace :=
  stage.traceValid

theorem totality : ∃ result : CT14.ExecutionResult
    (profile.capability ConcreteK4.surplusBase.problem) context,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace
      ConcreteK4.surplusBase.problem
      (profile.capability ConcreteK4.surplusBase.problem) context result.trace :=
  stage.total

theorem residualMass_exact : profile.residualMass = 4 := by
  native_decide

theorem globalSurplus_exact : profile.globalSurplus = 4 := by
  native_decide

/-- The semantic fan-mass inequality exported by the exact shared profile. -/
theorem semanticMassBound :
    profile.residualMass ≤
      (2 * profile.coefficient) * profile.globalSurplus :=
  stage.massBound

theorem checks_exact : profile.checks = 41 := by
  native_decide

theorem quadraticWork : profile.checks ≤
    3 * (profile.supports.card + 1) * (profile.occurrences.card + 1) :=
  stage.quadraticWorkBound

end EvenCycleExample.SupportIndexedFanMass
