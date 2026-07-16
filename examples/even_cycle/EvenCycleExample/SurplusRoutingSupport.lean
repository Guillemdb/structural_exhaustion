import EvenCycleExample.CT2Audit
import StructuralExhaustion.Graph.SurplusRoutingSupport

namespace EvenCycleExample.SurplusRoutingSupport

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u} packedStaticInput)
  (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u} packedStaticInput)}
variable {setup : Graph.SurplusPortActivation.Setup packedStaticInput ctx}
variable (stage : Graph.SurplusPortActivation.VerifiedActivatedStage
  packedStaticInput ctx setup)

/-!
Non-Erdős transfer for the support payload in the standard even-cycle
problem.  It is parameterized by one already verified surplus activation,
exactly as later consumers are; no Erdős target arithmetic is imported.
-/

abbrev Token := Graph.SurplusCapacityTokenRouting.Token
  (ctx := ctx) (setup := setup)

abbrev Pair := Graph.SurplusPairResponse.ScheduledPair (setup := setup)

theorem everyToken_has_exactRootSupport (token : Token (setup := setup)) :
    Graph.SurplusRoutingSupport.tokenRoot (ctx := ctx) (setup := setup) token ∈
      Graph.SurplusRoutingSupport.tokenSupport
        (ctx := ctx) (setup := setup) token :=
  Graph.SurplusRoutingSupport.tokenRoot_mem token

theorem everyPair_has_evidencePayload (pair : Pair (setup := setup)) :
    Nonempty (Graph.SurplusRoutingSupport.PairBranch stage pair) :=
  ⟨Graph.SurplusRoutingSupport.classify stage pair⟩

theorem freePayload_contains_both_demands (pair : Pair (setup := setup))
    (free : ¬(Graph.SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    (stage.demand pair.first).GammaVertices ⊆
        (Graph.SurplusRoutingSupport.PairBranch.free free).support stage ∧
      (stage.demand pair.second).GammaVertices ⊆
        (Graph.SurplusRoutingSupport.PairBranch.free free).support stage :=
  ⟨Graph.SurplusRoutingSupport.PairBranch.free_firstGamma_subset
      stage free,
    Graph.SurplusRoutingSupport.PairBranch.free_secondGamma_subset
      stage free⟩

/-- The blocked transfer retains the canonical first blocker and its exact
support, including the predecessor proof that no earlier candidate blocks. -/
theorem blockedPayload_has_canonicalFirstFidelity
    (pair : Pair (setup := setup))
    (blocked : (Graph.SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    let payload := Graph.SurplusRoutingSupport.PairBranch.blocked blocked
    payload.support stage =
        Graph.SurplusCapacityTokenRouting.supportVertices (setup := setup) pair
          (Graph.SurplusPairResponse.canonicalBlocker stage
            (Graph.SurplusRoutingSupport.PairBranch.blockedPair stage blocked)).value ∧
      (Graph.SurplusPairResponse.canonicalBlocker stage
          (Graph.SurplusRoutingSupport.PairBranch.blockedPair stage blocked)).value ∈
        ((Graph.SurplusPairResponse.localBlockerProfile stage).candidates pair).values ∧
      (Graph.SurplusPairResponse.localBlockerProfile stage).Blocks pair
        (Graph.SurplusPairResponse.canonicalBlocker stage
          (Graph.SurplusRoutingSupport.PairBranch.blockedPair stage blocked)).value ∧
      ∀ candidate ∈ (Graph.SurplusPairResponse.canonicalBlocker stage
          (Graph.SurplusRoutingSupport.PairBranch.blockedPair stage blocked)).before,
        ¬(Graph.SurplusPairResponse.localBlockerProfile stage).Blocks pair candidate := by
  refine ⟨rfl, ?_⟩
  exact Graph.SurplusRoutingSupport.PairBranch.blocked_canonical_sound stage blocked

/-- The transfer inherits the predecessor's literal blocker scan and its
existing polynomial enumeration bound. -/
theorem classificationSupport_has_practicalWork :
    Graph.SurplusRoutingSupport.classificationChecks stage =
        ((Graph.SurplusPairResponse.blockerFamily stage).pairs.orderedValues.map
          fun pair =>
            ((Graph.SurplusPairResponse.localBlockerProfile stage).candidates pair).values.length).sum ∧
      (Graph.SurplusPairResponse.pairEnumeration (setup := setup)).card ≤
        ctx.G.object.input.vertices.card ^ 4 :=
  Graph.SurplusRoutingSupport.classificationSupport_work stage

end EvenCycleExample.SurplusRoutingSupport
