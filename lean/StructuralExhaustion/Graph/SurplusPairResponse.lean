import StructuralExhaustion.Graph.FiniteConnector
import StructuralExhaustion.Graph.FiniteSupportResponse
import StructuralExhaustion.Graph.SurplusPairBlocker

namespace StructuralExhaustion.Graph.SurplusPairResponse

open StructuralExhaustion

universe u

/-!
# Exact free/blocked surplus-pair response stage

This module consumes one verified activation output.  It generates only the
canonically oriented pairs of the supplied surplus-slot schedule, executes the
local blocker scan on each pair, retains a shortest connector for each free
pair, and runs CT15 on the resulting exact finite-support response family.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

/-- The exact activated slot enumeration already used by CT6. -/
@[implicit_reducible]
def slotEnumeration : FinEnum (SurplusPortActivation.Slot setup) :=
  SurplusPortActivity.portSlots ctx.G.object

/-- Each unordered slot pair appears once, in source-enumeration order. -/
abbrev ScheduledPair :=
  Core.Enumeration.OrderedDistinctPair (slotEnumeration (setup := setup))

@[implicit_reducible]
def pairEnumeration : FinEnum (ScheduledPair (setup := setup)) :=
  Core.Enumeration.orderedDistinctPairs (slotEnumeration (setup := setup))

namespace ScheduledPair

def first (pair : ScheduledPair (setup := setup)) :
    SurplusPortActivation.Slot setup :=
  Core.Enumeration.OrderedDistinctPair.first pair

def second (pair : ScheduledPair (setup := setup)) :
    SurplusPortActivation.Slot setup :=
  Core.Enumeration.OrderedDistinctPair.second pair

theorem distinct (pair : ScheduledPair (setup := setup)) :
    pair.first ≠ pair.second :=
  Core.Enumeration.OrderedDistinctPair.distinct pair

/-- Forget only the scheduling-order proof; all pair-local graph data is
unchanged. -/
def toBlockerPair (pair : ScheduledPair (setup := setup)) :
    SurplusPairBlocker.Pair (setup := setup) where
  first := pair.first
  second := pair.second
  distinct := pair.distinct

end ScheduledPair

variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

/-- Pair-local blocker profile derived solely from the two activation rows. -/
noncomputable def localBlockerProfile :
    Core.FiniteBlockerLedger.Profile (ScheduledPair (setup := setup))
      (SurplusPairBlocker.Candidate ctx.G.Vertex) where
  candidates := fun pair ↦ pair.toBlockerPair.candidates stage
  Blocks := fun pair candidate ↦ pair.toBlockerPair.Blocks stage candidate
  blocksDecidable := by
    intro pair candidate
    exact (SurplusPairBlocker.Pair.profile stage).blocksDecidable
      pair.toBlockerPair candidate

/-- Exact family-level free/blocked split. -/
noncomputable def blockerFamily :
    Core.FiniteBlockerLedger.FamilyProfile
      (ScheduledPair (setup := setup))
      (SurplusPairBlocker.Candidate ctx.G.Vertex) where
  pairs := pairEnumeration (setup := setup)
  scan := localBlockerProfile stage

abbrev BlockedPair :=
  {pair : ScheduledPair (setup := setup) //
    (blockerFamily stage).HasBlocker pair}

abbrev FreePair :=
  {pair : ScheduledPair (setup := setup) //
    ¬(blockerFamily stage).HasBlocker pair}

@[implicit_reducible]
noncomputable def blockedPairEnumeration : FinEnum (BlockedPair stage) :=
  (blockerFamily stage).blockedPairs

@[implicit_reducible]
noncomputable def freePairEnumeration : FinEnum (FreePair stage) :=
  (blockerFamily stage).freePairs

/-- The canonical first local blocker retained for a blocked scheduled pair. -/
noncomputable def canonicalBlocker (pair : BlockedPair stage) :
    Core.FiniteSearch.FirstHit
      ((localBlockerProfile stage).candidates pair.1).values
      ((localBlockerProfile stage).Blocks pair.1) :=
  (blockerFamily stage).firstBlocker pair

theorem canonicalBlocker_sound (pair : BlockedPair stage) :
    (canonicalBlocker stage pair).value ∈
        ((localBlockerProfile stage).candidates pair.1).values ∧
      (localBlockerProfile stage).Blocks pair.1
        (canonicalBlocker stage pair).value ∧
      ∀ candidate ∈ (canonicalBlocker stage pair).before,
        ¬(localBlockerProfile stage).Blocks pair.1 candidate :=
  (blockerFamily stage).firstBlocker_sound pair

/-- Exact ledger partition at node `[130]`. -/
theorem blocked_card_add_free_card :
    (blockedPairEnumeration stage).card +
      (freePairEnumeration stage).card =
        (pairEnumeration (setup := setup)).card :=
  (blockerFamily stage).blocked_card_add_free_card

/-- The blocked and free branches cannot share a scheduled pair. -/
theorem free_blocked_disjoint (free : FreePair stage)
    (blocked : BlockedPair stage) : free.1 ≠ blocked.1 :=
  (blockerFamily stage).free_blocked_disjoint free blocked

/-- The pair schedule is at most quartic in the declared graph order because
the surplus-slot schedule is at most quadratic and each unordered pair is
generated once. -/
theorem pairEnumeration_card_le_fourthPower :
    (pairEnumeration (setup := setup)).card ≤
      ctx.G.object.input.vertices.card ^ 4 := by
  calc
    (pairEnumeration (setup := setup)).card ≤
        (slotEnumeration (setup := setup)).card ^ 2 :=
      Core.Enumeration.orderedDistinctPairs_card_le_square _
    _ ≤ (ctx.G.object.input.vertices.card ^ 2) ^ 2 :=
      Nat.pow_le_pow_left
        (SurplusPortActivity.portSlots_card_le_square ctx.G.object) 2
    _ = ctx.G.object.input.vertices.card ^ 4 := by ring

namespace FreePair

noncomputable def connector (pair : FreePair stage) :
    FiniteConnector.Certificate ctx.G.object
      (stage.demand pair.1.first).GammaVertices
      (stage.demand pair.1.second).GammaVertices :=
  FiniteConnector.canonical ctx.G.object
    (input.preconnected_of_noProperCore ctx)
    (stage.demand pair.1.first).GammaVertices_nonempty
    (stage.demand pair.1.second).GammaVertices_nonempty

/-- The exact support `X_π`: both response supports and one retained shortest
connector, with no connected-subgraph or path enumeration. -/
noncomputable def support (pair : FreePair stage) : Finset ctx.G.Vertex :=
  pair.connector stage |>.support

theorem firstGamma_subset_support (pair : FreePair stage) :
    (stage.demand pair.1.first).GammaVertices ⊆ pair.support stage :=
  (pair.connector stage).left_subset_support

theorem secondGamma_subset_support (pair : FreePair stage) :
    (stage.demand pair.1.second).GammaVertices ⊆ pair.support stage :=
  (pair.connector stage).right_subset_support

end FreePair

/-- Exact finite-support response profile for all and only blocker-free pairs. -/
noncomputable def responseProfile :
    FiniteSupportResponse.Profile input ctx (FreePair stage) where
  coordinates := freePairEnumeration stage
  support := fun pair ↦ pair.support stage

/-! The opaque profile boundary prevents theorem elaboration from repeatedly
normalizing the dependent free-pair enumeration and every local support.  The
CT15 result is an admissible-quotient rank ledger; Boolean-state realization is
a separate entropy contract. -/
noncomputable def responseCT15Profile :
    CT15.AdmissibleQuotient.Profile ctx :=
  (responseProfile stage).ct15Profile

noncomputable def verifiedCT15Stage :
    CT15.AdmissibleQuotient.VerifiedStage ctx :=
  (responseCT15Profile stage).verifiedStage

noncomputable def runCT15 := (responseCT15Profile stage).run

theorem runCT15_terminal : (runCT15 stage).terminal = .fullRankLedger :=
  (responseCT15Profile stage).terminal

theorem runCT15_trace : (runCT15 stage).trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] :=
  (responseCT15Profile stage).trace

/-- Complete verified quotient-rank output for the pair split: exact
partition, canonical blocked witnesses, exact free-pair supports, and CT15
full rank.  It does not assert realization of every joint Boolean response
vector required by manuscript node `[131]`. -/
structure VerifiedStage : Prop where
  partition : (blockedPairEnumeration stage).card +
    (freePairEnumeration stage).card =
      (pairEnumeration (setup := setup)).card
  disjoint : ∀ (free : FreePair stage) (blocked : BlockedPair stage),
    free.1 ≠ blocked.1
  blockedFirst : ∀ pair : BlockedPair stage,
    (canonicalBlocker stage pair).value ∈
        ((localBlockerProfile stage).candidates pair.1).values ∧
      (localBlockerProfile stage).Blocks pair.1
        (canonicalBlocker stage pair).value ∧
      ∀ candidate ∈ (canonicalBlocker stage pair).before,
        ¬(localBlockerProfile stage).Blocks pair.1 candidate
  firstSupport : ∀ pair : FreePair stage,
    (stage.demand pair.1.first).GammaVertices ⊆ pair.support stage
  secondSupport : ∀ pair : FreePair stage,
    (stage.demand pair.1.second).GammaVertices ⊆ pair.support stage
  ct15 : CT15.AdmissibleQuotient.VerifiedFor
    (responseCT15Profile stage)
  pairWork : (pairEnumeration (setup := setup)).card ≤
    ctx.G.object.input.vertices.card ^ 4
  localChecks : (blockerFamily stage).checks =
    ((blockerFamily stage).pairs.orderedValues.map fun pair ↦
      ((localBlockerProfile stage).candidates pair).values.length).sum

noncomputable def verifiedStage : VerifiedStage stage where
  partition := blocked_card_add_free_card stage
  disjoint := free_blocked_disjoint stage
  blockedFirst := canonicalBlocker_sound stage
  firstSupport := fun pair ↦ pair.firstGamma_subset_support stage
  secondSupport := fun pair ↦ pair.secondGamma_subset_support stage
  ct15 := (responseCT15Profile stage).verifiedFor
  pairWork := pairEnumeration_card_le_fourthPower
    (input := input) (ctx := ctx) (setup := setup)
  localChecks := (blockerFamily stage).checks_eq_sum

end StructuralExhaustion.Graph.SurplusPairResponse
