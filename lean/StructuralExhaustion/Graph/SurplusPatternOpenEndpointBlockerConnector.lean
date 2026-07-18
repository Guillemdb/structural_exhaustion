import StructuralExhaustion.Graph.SurplusPairBlocker
import StructuralExhaustion.Graph.SurplusPatternOpenEndpointFailure

namespace StructuralExhaustion.Graph.SurplusPatternOpenEndpointBlockerConnector

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

/-- Exact dependent identity between one raw separator port and one selected
active slot.  `HEq` is necessary because the port type is indexed by center. -/
structure SlotIdentification {center : ctx.G.Vertex}
    (raw : HighCenterPort.Port ctx.G.object center) : Type u where
  slot : SurplusPortActivation.Slot setup
  centerExact : slot.1 = center
  portExact : HEq (SurplusPortActivity.portOfSlot ctx.G.object slot) raw

/-- The exact missing provenance for the two raw ports of an activated local
failure.  No constructor is supplied from mere endpoint-support membership. -/
structure PairIdentification
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    (_activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second) : Type u where
  first : SlotIdentification (setup := setup) first
  second : SlotIdentification (setup := setup) second
  distinct : first.slot ≠ second.slot

namespace PairIdentification

variable {center : ctx.G.Vertex}
variable {centerHigh : 4 ≤ ctx.G.object.degree center}
variable {first second : HighCenterPort.Port ctx.G.object center}
variable {activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
  centerHigh setup.deletionCritical first second}

/-- Once the missing identities are furnished, they determine the exact
existing local blocker-pair input. -/
def blockerPair (identified : PairIdentification (setup := setup) activated) :
    SurplusPairBlocker.Pair (setup := setup) where
  first := identified.first.slot
  second := identified.second.slot
  distinct := identified.distinct

end PairIdentification

/-- Smallest honest node-[144] residual after local endpoint-failure
activation: the activated proof is present and selected-pair identity is the
named missing consumer. -/
structure ConnectorFrontier
    (setup : SurplusPortActivation.Setup input ctx)
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    (activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second) : Type u where
  activatedCopy : HighOpenEndpointFailure.ActivatedFailure input ctx center centerHigh
    setup.deletionCritical first second := activated

/-- The named missing consumer of a connector frontier. -/
def ConnectorFrontier.RequiredIdentification
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    {activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second}
    (_frontier : ConnectorFrontier setup activated) : Type u :=
  PairIdentification (setup := setup) activated

def frontier
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    (activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second) :
    ConnectorFrontier setup activated :=
  ⟨activated⟩

/-- Transporting the shared carrier into role labels is deliberately a
separate proof obligation.  This record is precisely the successful input to
the already existing blocker scan. -/
structure SharedCandidateWitness
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    {activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second}
    (identified : PairIdentification (setup := setup) activated) : Type u where
  candidate : SurplusPairBlocker.Candidate ctx.G.Vertex
  member : candidate ∈ (identified.blockerPair.candidates stage).values
  blocks : identified.blockerPair.Blocks stage candidate

/-- Execute the existing finite blocker consumer.  A supplied literal shared
candidate makes the `absent` branch contradictory, so the result is a
proof-carrying first blocker. -/
theorem execute
    (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
    {center : ctx.G.Vertex}
    {centerHigh : 4 ≤ ctx.G.object.degree center}
    {first second : HighCenterPort.Port ctx.G.object center}
    {activated : HighOpenEndpointFailure.ActivatedFailure input ctx center
      centerHigh setup.deletionCritical first second}
    (identified : PairIdentification (setup := setup) activated)
    (witness : SharedCandidateWitness stage identified) :
    ∃ hit : Core.FiniteSearch.FirstHit
        (identified.blockerPair.candidates stage).values
        (identified.blockerPair.Blocks stage),
      identified.blockerPair.run stage = .found hit := by
  rcases identified.blockerPair.stateSpace stage with found | absent
  · exact found
  · rcases absent with ⟨none, runExact⟩
    exact (none witness.candidate witness.member witness.blocks).elim

end StructuralExhaustion.Graph.SurplusPatternOpenEndpointBlockerConnector
