import Erdos64EG.Future.TypeBFanWholePortAssignment
import Erdos64EG.Future.CT10HighCenterPortDichotomy
import StructuralExhaustion.Graph.FanClosedPairAssembly

namespace Erdos64EG.Internal.TypeBFanCompatiblePairAssignment

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

open TypeBEntryRouting

abbrev Profile (residual : VerifiedNode64Residual ctx) :=
  TypeBFanShoulderIncidenceCoordinates.profile residual

abbrev OpenPort (residual : VerifiedNode64Residual ctx) :=
  Graph.FanClosedPort.OpenPort (Profile residual).centerHigh
    (Profile residual).deletionCritical

/-- Successful graph-derived whole-port assignment, with both exact ledgers
and the `FanClosed` proof retained. -/
structure ClosedOpenPort (residual : VerifiedNode64Residual ctx)
    (port : OpenPort residual) where
  first : TypeBFanWholePortAssignment.Assigned residual
    (Graph.InducedCoreFanAssignment.carrier ctx.G.object (Profile residual)
      port.1 Graph.InducedCoreFanAssignment.firstSide)
  second : TypeBFanWholePortAssignment.Assigned residual
    (Graph.InducedCoreFanAssignment.carrier ctx.G.object (Profile residual)
      port.1 Graph.InducedCoreFanAssignment.secondSide)
  firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
    (TypeBFanWholePortAssignment.coordinate residual port.1
      Graph.InducedCoreFanAssignment.firstSide)
  secondLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
    (TypeBFanWholePortAssignment.coordinate residual port.1
      Graph.InducedCoreFanAssignment.secondSide)
  closed : Graph.FanClosedPort.FanClosed (Profile residual).centerHigh
    (Profile residual).deletionCritical
    (TypeBFanWholePortAssignment.fanWindowProfile residual) port

/-- Exact first-missing whole-port residual. -/
inductive MissingOpenPort (residual : VerifiedNode64Residual ctx)
    (port : OpenPort residual) where
  | first
      (request : TypeBFanWholePortAssignment.MissingAssignmentRequest
        residual port.1)
      (side : request.side = Graph.InducedCoreFanAssignment.firstSide)
  | second
      (first : TypeBFanWholePortAssignment.Assigned residual
        (Graph.InducedCoreFanAssignment.carrier ctx.G.object (Profile residual)
          port.1 Graph.InducedCoreFanAssignment.firstSide))
      (firstLedger : TypeBFanIncidenceCoordinateLedger.IncidenceLedger residual
        (TypeBFanWholePortAssignment.coordinate residual port.1
          Graph.InducedCoreFanAssignment.firstSide))
      (request : TypeBFanWholePortAssignment.MissingAssignmentRequest
        residual port.1)
      (side : request.side = Graph.InducedCoreFanAssignment.secondSide)

inductive PortResult (residual : VerifiedNode64Residual ctx)
    (port : OpenPort residual) where
  | closed (proof : ClosedOpenPort residual port)
  | missing (residual : MissingOpenPort residual port)

noncomputable def classifyPort (residual : VerifiedNode64Residual ctx)
    (port : OpenPort residual) : PortResult residual port := by
  cases TypeBFanWholePortAssignment.classifyOpen residual port with
  | fanClosed first second firstLedger secondLedger closed =>
      exact .closed { first, second, firstLedger, secondLedger, closed }
  | firstMissing request side =>
      exact .missing (.first request side)
  | secondMissing first firstLedger request side =>
      exact .missing (.second first firstLedger request side)

/-- The successful pair branch contains the exact compatible pair, its two
graph-derived closed ports, the assembled `AssignedPair`, and the verified
constant-work CT5 stage. -/
structure ReadyPair (residual : VerifiedNode64Residual ctx) where
  degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center
  first : OpenPort residual
  second : OpenPort residual
  compatible : Graph.FanClosedPort.CompatiblePair
    (Profile residual).centerHigh (Profile residual).deletionCritical first second
  firstClosed : ClosedOpenPort residual first
  secondClosed : ClosedOpenPort residual second
  assembly : Graph.FanClosedPairAssembly.Assembly
    (base := fixedPackedInput ctx)
    (baseline := (packedStaticInput.fixedContext ctx).baseline)
    (Profile residual).centerHigh (Profile residual).deletionCritical
    (TypeBFanWholePortAssignment.fanWindowProfile residual)
    first second compatible firstClosed.closed secondClosed.closed

structure TriangularResidual (residual : VerifiedNode64Residual ctx) : Prop where
  degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center
  stage : HighCenterPortStage ctx residual.highSurplus.center
    residual.highSurplus.high
  many : ctx.G.object.degree residual.highSurplus.center - 2 ≤
    Fintype.card (Graph.HighCenterPort.TriangularPort ctx.G.object
      residual.highSurplus.center (Profile residual).centerHigh
      (Profile residual).deletionCritical)

/-- Exact manuscript handoff to the separate degree-four chain at nodes
`[78]`--`[80]`.  No compatible-pair conclusion is attached to this branch. -/
structure DegreeFourResidual (residual : VerifiedNode64Residual ctx) : Prop where
  stage : HighCenterPortStage ctx residual.highSurplus.center
    residual.highSurplus.high
  degreeFour : ctx.G.object.degree residual.highSurplus.center = 4

/-- Exact next-node route.  Assignment is attempted only after the local CT10
stage has produced a literal compatible pair. -/
inductive Route (residual : VerifiedNode64Residual ctx) where
  | degreeFour (result : DegreeFourResidual residual)
  | triangular (result : TriangularResidual residual)
  | firstPortMissing
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center)
      (first second : OpenPort residual)
      (compatible : Graph.FanClosedPort.CompatiblePair
        (Profile residual).centerHigh (Profile residual).deletionCritical
        first second)
      (missing : MissingOpenPort residual first)
  | secondPortMissing
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (degreeAboveFour : 4 < ctx.G.object.degree residual.highSurplus.center)
      (first second : OpenPort residual)
      (compatible : Graph.FanClosedPort.CompatiblePair
        (Profile residual).centerHigh (Profile residual).deletionCritical
        first second)
      (firstClosed : ClosedOpenPort residual first)
      (missing : MissingOpenPort residual second)
  | ready
      (stage : HighCenterPortStage ctx residual.highSurplus.center
        residual.highSurplus.high)
      (result : ReadyPair residual)

/-- Execute only the actual center's CT10 port schedule, then at most four
fixed carrier membership decisions. -/
noncomputable def route (residual : VerifiedNode64Residual ctx) : Route residual := by
  apply Classical.choose
  let stage := highCenterPort_stage ctx residual.highSurplus.center
    residual.highSurplus.high
  show ∃ result : Route residual, True
  by_cases degreeFour : ctx.G.object.degree residual.highSurplus.center = 4
  · exact ⟨.degreeFour { stage := stage, degreeFour := degreeFour }, trivial⟩
  · have degreeAboveFour :
        4 < ctx.G.object.degree residual.highSurplus.center := by
      have high := residual.highSurplus.high
      omega
    cases stage.dichotomy with
    | inr many =>
      exact ⟨.triangular {
        degreeAboveFour := degreeAboveFour
        stage := stage
        many := many }, trivial⟩
    | inl compatibleWitness =>
      obtain ⟨first, second, distinct, fanCompatible⟩ := compatibleWitness
      let pair : Graph.FanClosedPort.CompatiblePair
          (Profile residual).centerHigh (Profile residual).deletionCritical
          first second := ⟨distinct, fanCompatible⟩
      cases classifyPort residual first with
      | missing missing =>
          exact ⟨.firstPortMissing stage degreeAboveFour first second pair missing,
            trivial⟩
      | closed firstClosed =>
          cases classifyPort residual second with
          | missing missing =>
              exact ⟨.secondPortMissing stage degreeAboveFour first second pair
                firstClosed missing, trivial⟩
          | closed secondClosed =>
              exact ⟨.ready stage {
                degreeAboveFour := degreeAboveFour
                first := first
                second := second
                compatible := pair
                firstClosed := firstClosed
                secondClosed := secondClosed
                assembly := Graph.FanClosedPairAssembly.assemble
                  (base := fixedPackedInput ctx)
                  (baseline := (packedStaticInput.fixedContext ctx).baseline)
                  (Profile residual).centerHigh (Profile residual).deletionCritical
                  (TypeBFanWholePortAssignment.fanWindowProfile residual)
                  first second pair firstClosed.closed secondClosed.closed }, trivial⟩

def visibleChecks (residual : VerifiedNode64Residual ctx) : Nat :=
  Graph.HighCenterPort.classificationChecks ctx.G.object
      residual.highSurplus.center + 4

theorem visibleChecks_linear (residual : VerifiedNode64Residual ctx) :
    visibleChecks residual ≤
      2 * ctx.G.object.input.vertices.card + 6 := by
  unfold visibleChecks
  have bound : Graph.HighCenterPort.classificationChecks ctx.G.object
      residual.highSurplus.center ≤
        2 * ctx.G.object.input.vertices.card + 2 :=
    Graph.HighCenterPort.classificationChecks_linear ctx.G.object
      residual.highSurplus.center
  omega

end Erdos64EG.Internal.TypeBFanCompatiblePairAssignment
