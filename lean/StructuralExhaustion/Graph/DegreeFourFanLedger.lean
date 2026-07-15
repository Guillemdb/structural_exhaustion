import Mathlib.Tactic
import StructuralExhaustion.Graph.AssignedFanCharge
import StructuralExhaustion.Graph.CertificateClosedFanCharge

namespace StructuralExhaustion.Graph.DegreeFourFanLedger

open StructuralExhaustion

universe u uAmbient uBranch

/-!
# The exact degree-four fan ledger

This is the local CT14 contract used after a high-centre degree split has
returned its degree-four branch.  The member universe consists only of the
ports incident with the selected centre.  A port is closed precisely when
both of its non-centre incidences belong to the supplied assignment.

The framework computes the closed-port count `c`.  From the incoming equality
`degree center = 4` it then derives the complete five-row ledger, including
the centre surplus, the sign split at `c = 2`, and the exact seven-quarter-unit
B1 slack.  No ambient graph, subgraph, path, or assignment universe is
enumerated.
-/

variable {V : Type u}
variable (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
variable (Assigned : FanClosedPort.LocalCarrier V → Prop)
variable (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))

/-- CT14 profile on the literal incident-port schedule of one centre. -/
def profile : CertificateClosedFanCharge.Profile
    (HighCenterPort.Port object center) where
  members := HighCenterPort.ports object center
  Closed := AssignedFanCharge.CubicClosed object center Assigned
  closedDecidable := AssignedFanCharge.cubicClosedDecidable object center
    Assigned assignedDecidable
  quarterCharge := AssignedFanCharge.quarterCharge object center centerHigh
    deletionCritical Assigned assignedDecidable
  closedQuarterCharge := fun port closed =>
    AssignedFanCharge.quarterCharge_eq_neg_one_of_cubicClosed object center
      centerHigh deletionCritical Assigned assignedDecidable port closed
  openQuarterChargeLower := fun port openPort =>
    AssignedFanCharge.quarterCharge_ge_three_of_not_cubicClosed object center
      centerHigh deletionCritical Assigned assignedDecidable port openPort

theorem members_card_eq_degree :
    (profile object center centerHigh deletionCritical Assigned
      assignedDecidable).members.card = object.degree center :=
  HighCenterPort.ports_card_eq_degree object center

def closedCount {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Nat :=
  (profile object center centerHigh deletionCritical Assigned
    assignedDecidable).closedCount context

/-- Four times the manuscript deficit `D_B = c - 7/4`. -/
def quarterDeficit {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Int :=
  4 * (closedCount object center centerHigh deletionCritical Assigned
    assignedDecidable context : Int) + (object.degree center : Int) - 11

/-- Primitive local checks: at most one declared-vertex scan for each
incident port, three constant CT14 passes per port, and one comparison. -/
def checks : Nat :=
  object.degree center * object.input.vertices.card +
    3 * object.degree center + 1

structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (degreeFour : object.degree center = 4) : Prop where
  execution : (profile object center centerHigh deletionCritical Assigned
    assignedDecidable).VerifiedStage context
  verified : ((profile object center centerHigh deletionCritical Assigned
    assignedDecidable).run context).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace P
    ((profile object center centerHigh deletionCritical Assigned
      assignedDecidable).capability P) context
    ((profile object center centerHigh deletionCritical Assigned
      assignedDecidable).run context).trace
  total : ∃ result : CT14.ExecutionResult
      ((profile object center centerHigh deletionCritical Assigned
        assignedDecidable).capability P) context,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace P
      ((profile object center centerHigh deletionCritical Assigned
        assignedDecidable).capability P) context result.trace
  centerSurplus : object.degree center - 3 = 1
  closedCountLeFour : closedCount object center centerHigh deletionCritical
    Assigned assignedDecidable context ≤ 4
  exactCases :
    closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context = 0 ∨
      closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context = 1 ∨
      closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context = 2 ∨
      closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context = 3 ∨
      closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context = 4
  exactDeficit : quarterDeficit object center centerHigh deletionCritical
      Assigned assignedDecidable context =
    4 * (closedCount object center centerHigh deletionCritical Assigned
      assignedDecidable context : Int) - 7
  signSplit :
    (closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context ≤ 1 ∧
      quarterDeficit object center centerHigh deletionCritical Assigned
        assignedDecidable context ≤ 0) ∨
    (2 ≤ closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context ∧
      0 < quarterDeficit object center centerHigh deletionCritical Assigned
        assignedDecidable context)
  b1Slack :
    4 * (closedCount object center centerHigh deletionCritical Assigned
        assignedDecidable context : Int) -
      quarterDeficit object center centerHigh deletionCritical Assigned
        assignedDecidable context = 7
  polynomial : checks object center ≤
    17 * (object.input.vertices.card + 1)

def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (degreeFour : object.degree center = 4) :
    VerifiedStage object center centerHigh deletionCritical Assigned
      assignedDecidable context degreeFour := by
  let fanProfile := profile object center centerHigh deletionCritical Assigned
    assignedDecidable
  have countLe : closedCount object center centerHigh deletionCritical Assigned
      assignedDecidable context ≤ 4 := by
    have bound := fanProfile.closedCount_le_card context
    rw [members_card_eq_degree object center centerHigh deletionCritical
      Assigned assignedDecidable, degreeFour] at bound
    exact bound
  have split :
      closedCount object center centerHigh deletionCritical Assigned
          assignedDecidable context ≤ 1 ∨
        2 ≤ closedCount object center centerHigh deletionCritical Assigned
          assignedDecidable context := by omega
  refine {
    execution := fanProfile.verifiedStage context
    verified := CT14.run_verified _ _ (fanProfile.input context)
    traceValid := CT14.run_trace_valid _ _ (fanProfile.input context)
    total := CT14.run_total (fanProfile.capability P) context
      (fanProfile.input context)
    centerSurplus := by omega
    closedCountLeFour := countLe
    exactCases := by omega
    exactDeficit := by simp only [quarterDeficit, degreeFour]; omega
    signSplit := ?_
    b1Slack := by simp only [quarterDeficit, degreeFour]; omega
    polynomial := by simp [checks, degreeFour]; omega
  }
  rcases split with small | large
  · exact Or.inl ⟨small, by
      simp only [quarterDeficit, degreeFour]
      omega⟩
  · exact Or.inr ⟨large, by
      simp only [quarterDeficit, degreeFour]
      omega⟩

end StructuralExhaustion.Graph.DegreeFourFanLedger
