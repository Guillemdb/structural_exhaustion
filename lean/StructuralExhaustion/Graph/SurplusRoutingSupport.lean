import StructuralExhaustion.Graph.SurplusCapacityTokenRouting

namespace StructuralExhaustion.Graph.SurplusRoutingSupport

open StructuralExhaustion

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}

abbrev Token := SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)
abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)

/-!
# Exact supports feeding same-token routing

This module is deliberately predecessor-only.  It exposes the literal finite
support already present in every capacity-token constructor and packages the
decidable free/blocked split of one scheduled pair with the corresponding
retained support.  It does not build the later connected closure `Z`.
-/

/-- Literal root vertex of each capacity-token constructor. -/
noncomputable def tokenRoot : Token (ctx := ctx) (setup := setup) → ctx.G.Vertex
  | .inl token =>
      InducedPathWindowLedger.selectedWindow ctx.G.object token.1 token.2.1
  | .inr (.inl token) => token.1.1
  | .inr (.inr (.inl vertex)) => vertex
  | .inr (.inr (.inr (.inl dart))) => dart.fst
  | .inr (.inr (.inr (.inr slot))) =>
      SurplusPortActivity.portEndpoint ctx.G.object slot

/-- Literal finite support of each capacity-token constructor. -/
noncomputable def tokenSupport :
    Token (ctx := ctx) (setup := setup) → Finset ctx.G.Vertex := by
  classical
  intro token
  rcases token with window | remainderOrPrimitive
  · exact {InducedPathWindowLedger.selectedWindow ctx.G.object
      window.1 window.2.1, window.2.2.1}
  · rcases remainderOrPrimitive with remainder | primitive
    · exact {remainder.1.1}
    · rcases primitive with vertex | incidenceOrPort
      · exact {vertex}
      · rcases incidenceOrPort with dart | slot
        · exact dart.edge.toFinset
        · exact SurplusPortActivation.PortSupport setup slot

/-- The manuscript root selected for a token belongs to its exact support. -/
theorem tokenRoot_mem (token : Token (ctx := ctx) (setup := setup)) :
    tokenRoot (ctx := ctx) (setup := setup) token ∈
      tokenSupport (ctx := ctx) (setup := setup) token := by
  classical
  rcases token with window | remainderOrPrimitive
  · simp [tokenSupport, tokenRoot]
  · rcases remainderOrPrimitive with remainder | primitive
    · simp [tokenSupport, tokenRoot]
    · rcases primitive with vertex | incidenceOrPort
      · simp [tokenSupport, tokenRoot]
      · rcases incidenceOrPort with dart | slot
        · change dart.fst ∈ dart.edge.toFinset
          rw [Sym2.mem_toFinset]
          change dart.fst ∈ s(dart.fst, dart.snd)
          rw [Sym2.mem_iff]
          exact Or.inl rfl
        · simpa [tokenSupport, tokenRoot,
            SurplusPortActivation.portVertex] using
            SurplusPortActivation.portVertex_mem_portSupport setup slot
              SurplusPortActivation.PortRole.buffer

variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

/-- The decidable node-[130] branch, retaining evidence rather than merely a
role equality. -/
inductive PairBranch (pair : Pair (setup := setup)) : Type u where
  | blocked (evidence : (SurplusPairResponse.blockerFamily stage).HasBlocker pair)
  | free (evidence : ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair)

/-- Execute the existing decidable split exactly once. -/
noncomputable def classify (pair : Pair (setup := setup)) :
    PairBranch stage pair :=
  match (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair with
  | .isTrue evidence => .blocked evidence
  | .isFalse evidence => .free evidence

namespace PairBranch

def blockedPair {pair : Pair (setup := setup)}
    (evidence : (SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    SurplusPairResponse.BlockedPair (setup := setup) stage :=
  ⟨pair, evidence⟩

def freePair {pair : Pair (setup := setup)}
    (evidence : ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    SurplusPairResponse.FreePair (setup := setup) stage :=
  ⟨pair, evidence⟩

/-- Exact finite pair support selected by the retained branch evidence:
canonical first-blocker support on the blocked branch, and the already
retained shortest-connector support on the free branch. -/
noncomputable def support {pair : Pair (setup := setup)} :
    PairBranch stage pair → Finset ctx.G.Vertex
  | .blocked evidence =>
      let blocked := blockedPair stage evidence
      SurplusCapacityTokenRouting.supportVertices (setup := setup) pair
        (SurplusPairResponse.canonicalBlocker stage blocked).value
  | .free evidence =>
      let free := freePair stage evidence
      free.support stage

/-- Blocked payload exposes the actual canonical first hit used to define its
support. -/
noncomputable def canonicalBlocker {pair : Pair (setup := setup)}
    (branch : PairBranch stage pair) :
    Option (SurplusPairBlocker.Candidate ctx.G.Vertex) :=
  match branch with
  | .blocked evidence =>
      some (SurplusPairResponse.canonicalBlocker stage
        (blockedPair stage evidence)).value
  | .free _ => none

/-- Free payload exposes the exact retained connector; no connector is
fabricated on the blocked branch. -/
noncomputable def connectorSupport {pair : Pair (setup := setup)}
    (branch : PairBranch stage pair) : Option (Finset ctx.G.Vertex) :=
  match branch with
  | .blocked _ => none
  | .free evidence => some
      (SurplusPairResponse.FreePair.support stage (freePair stage evidence))

@[simp]
theorem support_blocked {pair : Pair (setup := setup)}
    (evidence : (SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    support stage (.blocked evidence) =
      SurplusCapacityTokenRouting.supportVertices (setup := setup) pair
        (SurplusPairResponse.canonicalBlocker stage
          (blockedPair stage evidence)).value :=
  rfl

@[simp]
theorem support_free {pair : Pair (setup := setup)}
    (evidence : ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    support stage (.free evidence) =
      SurplusPairResponse.FreePair.support stage (freePair stage evidence) :=
  rfl

theorem free_firstGamma_subset {pair : Pair (setup := setup)}
    (evidence : ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    (stage.demand pair.first).GammaVertices ⊆
      support stage (.free evidence) :=
  SurplusPairResponse.FreePair.firstGamma_subset_support stage
    (freePair stage evidence)

theorem free_secondGamma_subset {pair : Pair (setup := setup)}
    (evidence : ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    (stage.demand pair.second).GammaVertices ⊆
      support stage (.free evidence) :=
  SurplusPairResponse.FreePair.secondGamma_subset_support stage
    (freePair stage evidence)

/-- Canonical-first fidelity of a blocked payload. -/
theorem blocked_canonical_sound {pair : Pair (setup := setup)}
    (evidence : (SurplusPairResponse.blockerFamily stage).HasBlocker pair) :
    let blocked := blockedPair stage evidence
    (SurplusPairResponse.canonicalBlocker stage blocked).value ∈
        ((SurplusPairResponse.localBlockerProfile stage).candidates pair).values ∧
      (SurplusPairResponse.localBlockerProfile stage).Blocks pair
        (SurplusPairResponse.canonicalBlocker stage blocked).value ∧
      ∀ candidate ∈ (SurplusPairResponse.canonicalBlocker stage blocked).before,
        ¬(SurplusPairResponse.localBlockerProfile stage).Blocks pair candidate :=
  SurplusPairResponse.canonicalBlocker_sound stage (blockedPair stage evidence)

end PairBranch

/-- Classification uses exactly the predecessor blocker-family audit. Support
projection then reuses the retained canonical blocker or free connector and
does not perform another search. -/
noncomputable def classificationChecks : Nat :=
  (SurplusPairResponse.blockerFamily stage).checks

theorem classificationSupport_work :
    classificationChecks stage =
        ((SurplusPairResponse.blockerFamily stage).pairs.orderedValues.map
          fun pair =>
            ((SurplusPairResponse.localBlockerProfile stage).candidates pair).values.length).sum ∧
      (SurplusPairResponse.pairEnumeration (setup := setup)).card ≤
        ctx.G.object.input.vertices.card ^ 4 :=
  ⟨(SurplusPairResponse.blockerFamily stage).checks_eq_sum,
    SurplusPairResponse.pairEnumeration_card_le_fourthPower⟩

end StructuralExhaustion.Graph.SurplusRoutingSupport
