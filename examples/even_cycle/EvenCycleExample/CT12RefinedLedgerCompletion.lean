import EvenCycleExample.Concrete
import StructuralExhaustion.CT12.RefinedLedgerCompletion
import StructuralExhaustion.Core.DependentWeightedSelection
import StructuralExhaustion.Core.FiniteWeightedSelection

namespace EvenCycleExample.RefinedLedgerFixture

open StructuralExhaustion
open EvenCycleExample.ConcreteK4

/-- A literal singleton weighted selection at each demand. -/
def localSelection (demand : Bool) :
    Core.FiniteWeightedSelection.Profile Unit Vertex where
  items := Core.Enumeration.unit
  carrierDecidableEq := inferInstance
  mandatory := fun _item => True
  mandatoryDecidable := fun _item => inferInstance
  forbidden := fun _item => False
  forbiddenDecidable := fun _item => inferInstance
  weight := fun _item => 0
  required := 0
  baseSupport := if demand then {.v0} else {.v1}
  itemSupport := fun _item => ∅

/-- A non-Erdős two-demand family verifying transfer of the framework's
dependent weighted-selection adapter. -/
def family : Core.DependentWeightedSelection.Profile Bool Vertex where
  Item := fun _demand => Unit
  demands := Core.Enumeration.bool
  selection := localSelection

noncomputable def profile : CT12.RefinedLedgerCompletion.Profile Bool Vertex :=
  family.refinedLedger

def stage := profile.verifiedStage (Graph.FiniteObject.context object)

theorem exhausted : (profile.run
    (Graph.FiniteObject.context object)).terminal = .exhausted :=
  stage.terminal

theorem iterations_exact : (profile.run
    (Graph.FiniteObject.context object)).iterations = profile.demands.card :=
  stage.iterationsExact

theorem choice_or_minimal_obstruction : Nonempty profile.FullChoice ∨
    ∃ selected, selected.Sublist profile.fullSchedule ∧
      profile.MinimalOverlapObstruction selected :=
  stage.minimalAlternative

theorem one_demand_support_mono : profile.overlapSupport [false] ⊆
    profile.overlapSupport profile.fullSchedule := by
  apply profile.overlapSupport_mono
  simp [Core.FiniteRefinedLedger.Profile.fullSchedule, profile]

/-! The same external example checks the proof-level weighted candidate fibre
used by the Erdős positive-fan specialization. -/

def weightedProfile : Core.FiniteWeightedSelection.Profile Bool Vertex where
  items := Core.Enumeration.bool
  carrierDecidableEq := inferInstance
  mandatory := fun item => item = true
  mandatoryDecidable := fun _item => inferInstance
  forbidden := fun _item => False
  forbiddenDecidable := fun _item => inferInstance
  weight := fun item => if item then 2 else 1
  required := 3
  baseSupport := {.v0}
  itemSupport := fun item => if item then {.v1} else {.v2}

noncomputable def weightedCandidate : weightedProfile.Candidate :=
  weightedProfile.allItemsCandidate (fun _item => by simp [weightedProfile])
    (by decide)

theorem weighted_candidate_pays :
    (3 : Int) ≤ ∑ item ∈ weightedCandidate.1,
      weightedProfile.weight item :=
  weightedProfile.payment weightedCandidate

theorem weighted_candidate_supports_base :
    Vertex.v0 ∈ weightedProfile.carrierSupport weightedCandidate := by
  apply weightedProfile.baseSupport_subset
  simp [weightedProfile]

end EvenCycleExample.RefinedLedgerFixture
