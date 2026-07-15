import StructuralExhaustion.CT9.TokenRoleLedger
import StructuralExhaustion.Graph.SurplusPairResponse
import StructuralExhaustion.Graph.SurplusTokenRole

namespace StructuralExhaustion.Graph.SurplusPairTokenRouting

open StructuralExhaustion

universe u

/-!
# Total routing of the free/blocked surplus-pair split

The blocker scan already partitions the canonical pair schedule.  This module
gives every scheduled pair an initial selected-port token, namely its first
endpoint.  A blocked pair retains the kind of its canonical first blocker; a
free pair receives the distinct `freeAnchor` role.  The resulting CT9 product
ledger is total, so no pair is lost while the blocked subtype is subsequently
retokenized by its blocker carrier.

No Boolean realization, geometric closure, or additional graph hypothesis is
part of this routing theorem.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev BlockedPair := SurplusPairResponse.BlockedPair stage
abbrev FreePair := SurplusPairResponse.FreePair stage
abbrev Token := SurplusPortActivation.Slot setup
abbrev Role := SurplusTokenRole.PairRouteRole

@[implicit_reducible]
noncomputable def tokens : FinEnum (Token (setup := setup)) :=
  SurplusPairResponse.slotEnumeration (setup := setup)

@[implicit_reducible]
noncomputable def pairs : FinEnum (Pair (setup := setup)) :=
  SurplusPairResponse.pairEnumeration (setup := setup)

/-- Initial token used to make the node `[130]` route total. -/
def pairToken (pair : Pair (setup := setup)) : Token (setup := setup) :=
  pair.first

/-- Exact role of one scheduled pair.  The blocked constructor is computed
from the already selected canonical blocker; the free constructor carries no
blocker value. -/
noncomputable def pairRole (pair : Pair (setup := setup)) : Role :=
  match (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair with
  | .isTrue blocked =>
      let first := SurplusPairResponse.canonicalBlocker stage ⟨pair, blocked⟩
      .blocked (SurplusTokenRole.admittedKind first.value)
  | .isFalse _notBlocked => .freeAnchor

noncomputable def capability : CT9.Capability input.problem :=
  CT9.TokenRoleLedger.capability input.problem (Pair (setup := setup))
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)

noncomputable def ct9Input : CT9.Input (capability stage) :=
  CT9.TokenRoleLedger.input
    (capacity := fun _ _ ↦ 0) ctx.toBranchContext
    (pairs (setup := setup)).toOrderedCollection

/-- Exact CT9 execution on the complete scheduled-pair product ledger. -/
noncomputable def run :=
  CT9.TokenRoleLedger.run
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

theorem run_verified : (run stage).outcome.Valid :=
  CT9.TokenRoleLedger.run_verified
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

theorem run_traceValid :
    CT9.Graph.ValidTrace (capability stage) (ct9Input stage)
      (run stage).trace :=
  CT9.TokenRoleLedger.run_traceValid
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

theorem run_terminal_exhaustive :
    (run stage).terminal = .overloaded ∨
      (run stage).terminal = .bounded :=
  CT9.TokenRoleLedger.run_terminal_exhaustive
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

theorem run_total : ∃ result,
    result = run stage ∧ result.outcome.Valid ∧
      CT9.Graph.ValidTrace (capability stage) (ct9Input stage) result.trace :=
  CT9.TokenRoleLedger.run_total
    (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
    (pairToken (setup := setup)) (pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

/-- Every scheduled pair appears in exactly one initial token--role fibre. -/
theorem noOvercounting :
    (ct9Input stage).items.values.length =
      ((capability stage).labels.orderedValues.map fun labelValue ↦
        CT9.fibreCount (capability stage) (ct9Input stage) labelValue).sum :=
  CT9.cardinality_eq_sum_fibreCount (capability stage) (ct9Input stage)

/-- If every initial token--role fibre has a supplied local bound, CT9 turns
those local checks into a bound for the complete scheduled-pair family. -/
theorem bounded_total (bound : Nat)
    (bounded : ∀ token role,
      CT9.fibreCount (capability stage) (ct9Input stage) (token, role) ≤ bound) :
    (ct9Input stage).items.values.length ≤
      bound * ((tokens (setup := setup)).card * 5) := by
  change (pairs (setup := setup)).toOrderedCollection.values.length ≤
    bound * ((tokens (setup := setup)).card * 5)
  simpa [SurplusTokenRole.pairRouteRole_card] using
    CT9.TokenRoleLedger.bounded_total
      (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
      (pairToken (setup := setup)) (pairRole stage)
      ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection
      bound bounded

/-- The initial item collection is definitionally the pair schedule emitted
by node `[130]`. -/
theorem input_items_eq_pair_schedule :
    (ct9Input stage).items =
      (SurplusPairResponse.pairEnumeration
        (setup := setup)).toOrderedCollection :=
  rfl

/-- A pair classified free by node `[130]` has exactly the new free-anchor
role in the total ledger. -/
theorem free_role (pair : FreePair stage) :
    pairRole stage pair.1 = .freeAnchor := by
  unfold pairRole
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair.1 with
  | isTrue blocked => exact (pair.2 blocked).elim
  | isFalse _notBlocked => rfl

/-- A blocked pair retains the exact kind of its canonical first blocker. -/
theorem blocked_role (pair : BlockedPair stage) :
    pairRole stage pair.1 =
      .blocked (SurplusTokenRole.admittedKind
        (SurplusPairResponse.canonicalBlocker stage pair).value) := by
  unfold pairRole
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair.1 with
  | isTrue _blocked => simp
  | isFalse notBlocked => exact (notBlocked pair.2).elim

/-- Seeing the `freeAnchor` label is equivalent to the negative side of the
actual blocker scan; it is not an added assumption. -/
theorem free_of_role_eq (pair : Pair (setup := setup))
    (roleEq : pairRole stage pair = .freeAnchor) :
    ¬(SurplusPairResponse.blockerFamily stage).HasBlocker pair := by
  unfold pairRole at roleEq
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair with
  | isTrue _blocked => simp [decision] at roleEq
  | isFalse notBlocked => exact notBlocked

/-- Fibre membership exposes both authored coordinates. -/
theorem fields_of_mem_fibre
    {pair : Pair (setup := setup)} {token : Token (setup := setup)} {role : Role}
    (member : pair ∈ CT9.fibre (capability stage) (ct9Input stage)
      (token, role)) :
    pair.first = token ∧ pairRole stage pair = role := by
  exact CT9.TokenRoleLedger.coordinates_of_mem_fibre
    (tokens := tokens (setup := setup))
    (roles := SurplusTokenRole.pairRouteRoleEnum)
    (token := pairToken (setup := setup)) (role := pairRole stage)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection member

/-- Every item in a `freeAnchor` fibre reconstructs the exact free-pair
subtype consumed by the connector/geometric branch. -/
def freePairOfMemFreeAnchor
    {pair : Pair (setup := setup)} {token : Token (setup := setup)}
    (member : pair ∈ CT9.fibre (capability stage) (ct9Input stage)
      (token, .freeAnchor)) : FreePair stage :=
  ⟨pair, free_of_role_eq stage pair (fields_of_mem_fibre stage member).2⟩

/-- Two free-anchor fibre members form a literal scheduled-pair star. -/
theorem same_anchor_of_mem_freeAnchor
    {left right : Pair (setup := setup)} {token : Token (setup := setup)}
    (leftMember : left ∈ CT9.fibre (capability stage) (ct9Input stage)
      (token, .freeAnchor))
    (rightMember : right ∈ CT9.fibre (capability stage) (ct9Input stage)
      (token, .freeAnchor)) :
    left.first = right.first := by
  exact (fields_of_mem_fibre stage leftMember).1.trans
    (fields_of_mem_fibre stage rightMember).1.symm

/-- One exact member of the computed `freeAnchor` fibre passed to the
primitive selected-port audit.  The full finite fibre remains the CT9 list in
`member`; no second list or ambient graph family is materialized. -/
structure FreeAnchorMember (token : Token (setup := setup)) where
  pair : Pair (setup := setup)
  member : pair ∈ CT9.fibre (capability stage) (ct9Input stage)
    (token, .freeAnchor)

/-- Complete finite input of one primitive selected-port audit.  `items` is
definitionally the computed CT9 fibre; the equality prevents an application
from replacing it by a chosen subfamily. -/
structure PrimitiveAuditInput where
  token : Token (setup := setup)
  items : List (Pair (setup := setup))
  exact_items : items = CT9.fibre (capability stage) (ct9Input stage)
    (token, .freeAnchor)

noncomputable def primitiveAuditInput (token : Token (setup := setup)) :
    PrimitiveAuditInput stage where
  token := token
  items := CT9.fibre (capability stage) (ct9Input stage)
    (token, .freeAnchor)
  exact_items := rfl

namespace FreeAnchorMember

def toFreePair {token : Token (setup := setup)}
    (item : FreeAnchorMember stage token) : FreePair stage :=
  freePairOfMemFreeAnchor stage item.member

/-- The shortest connector already retained at node `[130]`; routing to the
primitive audit does not search a new path family. -/
noncomputable def connector {token : Token (setup := setup)}
    (item : FreeAnchorMember stage token) :=
  item.toFreePair.connector stage

theorem firstGamma_subset_connectorSupport
    {token : Token (setup := setup)} (item : FreeAnchorMember stage token) :
    (stage.demand item.pair.first).GammaVertices ⊆
      item.toFreePair.support stage :=
  item.toFreePair.firstGamma_subset_support stage

theorem secondGamma_subset_connectorSupport
    {token : Token (setup := setup)} (item : FreeAnchorMember stage token) :
    (stage.demand item.pair.second).GammaVertices ⊆
      item.toFreePair.support stage :=
  item.toFreePair.secondGamma_subset_support stage

end FreeAnchorMember

/-- Every item handed to the primitive selected-port audit is genuinely on
the negative side of the canonical blocker scan. -/
theorem freeAnchorFibre_member_is_free
    {token : Token (setup := setup)} (item : FreeAnchorMember stage token) :
    ¬(SurplusPairResponse.blockerFamily stage).HasBlocker item.pair := by
  exact (freePairOfMemFreeAnchor stage item.member).2

/-- The primitive token in the handoff is literally the first selected port
of every residual pair. -/
theorem freeAnchorFibre_member_first
    {token : Token (setup := setup)} (item : FreeAnchorMember stage token) :
    item.pair.first = token :=
  (fields_of_mem_fibre stage item.member).1

/-- The blocked side of the route retains the complete first-hit certificate,
including absence of every earlier blocker candidate. -/
theorem blocked_retains_canonical_blocker (pair : BlockedPair stage) :
    (SurplusPairResponse.canonicalBlocker stage pair).value ∈
        ((SurplusPairResponse.localBlockerProfile stage).candidates pair.1).values ∧
      (SurplusPairResponse.localBlockerProfile stage).Blocks pair.1
        (SurplusPairResponse.canonicalBlocker stage pair).value ∧
      ∀ candidate ∈ (SurplusPairResponse.canonicalBlocker stage pair).before,
        ¬(SurplusPairResponse.localBlockerProfile stage).Blocks pair.1 candidate :=
  SurplusPairResponse.canonicalBlocker_sound stage pair

/-- The route introduces no new token supply: its tokens are precisely the
activated selected-surplus-port schedule. -/
theorem token_card_eq_slots :
    (tokens (setup := setup)).card =
      (SurplusPairResponse.slotEnumeration (setup := setup)).card :=
  rfl

/-- The role alphabet is fixed independently of the graph. -/
theorem role_card : SurplusTokenRole.pairRouteRoleEnum.card = 5 :=
  SurplusTokenRole.pairRouteRole_card

/-- Routing scans the explicit pair list against the selected-port token list
and the fixed role alphabet. -/
noncomputable def checks
    (_stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup) : Nat :=
  CT9.TokenRoleLedger.checks (tokens (setup := setup))
    SurplusTokenRole.pairRouteRoleEnum
    (pairs (setup := setup)).toOrderedCollection

theorem checks_eq :
    checks stage = (pairs (setup := setup)).card *
      ((tokens (setup := setup)).card * 5) := by
  simpa [checks, SurplusTokenRole.pairRouteRole_card] using
    (CT9.TokenRoleLedger.checks_enumeration_eq
      (tokens (setup := setup)) SurplusTokenRole.pairRouteRoleEnum
      (pairs (setup := setup)))

/-- The complete product scan is bounded by `5 n⁶`: at most `n⁴`
scheduled pairs are tested against at most `n²` selected-port tokens and the
fixed five-role alphabet. -/
theorem checks_le_five_mul_sixthPower :
    checks stage ≤ 5 * ctx.G.object.input.vertices.card ^ 6 := by
  rw [checks_eq]
  have pairBound : (pairs (setup := setup)).card ≤
      ctx.G.object.input.vertices.card ^ 4 :=
    SurplusPairResponse.pairEnumeration_card_le_fourthPower
      (input := input) (ctx := ctx) (setup := setup)
  have tokenBound : (tokens (setup := setup)).card ≤
      ctx.G.object.input.vertices.card ^ 2 := by
    exact SurplusPortActivity.portSlots_card_le_square ctx.G.object
  calc
    (pairs (setup := setup)).card *
        ((tokens (setup := setup)).card * 5) ≤
      ctx.G.object.input.vertices.card ^ 4 *
        (ctx.G.object.input.vertices.card ^ 2 * 5) :=
      Nat.mul_le_mul pairBound (Nat.mul_le_mul tokenBound (le_refl 5))
    _ = 5 * ctx.G.object.input.vertices.card ^ 6 := by ring

/-- Sharper local bound available whenever an application has already proved
that its residual token schedule has size at most `size`.  The pair schedule
then has size at most `size²`, so the product CT9 audit uses at most
`5 * size³` checks. -/
theorem checks_le_five_mul_cube_of_token_card_le (size : Nat)
    (tokenBound : (tokens (setup := setup)).card ≤ size) :
    checks stage ≤ 5 * size ^ 3 := by
  rw [checks_eq]
  have pairTokenBound : (pairs (setup := setup)).card ≤
      (tokens (setup := setup)).card ^ 2 :=
    Core.Enumeration.orderedDistinctPairs_card_le_square
      (tokens (setup := setup))
  have pairBound : (pairs (setup := setup)).card ≤ size ^ 2 :=
    pairTokenBound.trans (Nat.pow_le_pow_left tokenBound 2)
  calc
    (pairs (setup := setup)).card *
        ((tokens (setup := setup)).card * 5) ≤
      size ^ 2 * (size * 5) :=
      Nat.mul_le_mul pairBound (Nat.mul_le_mul tokenBound (le_refl 5))
    _ = 5 * size ^ 3 := by ring

/-- Complete reusable graph contract for the node-[130] free/blocked product
route.  It owns the CT9 execution, exact partition, typed handoffs, and the
polynomial work bound. -/
structure VerifiedStage : Prop where
  terminal : (run stage).terminal = .overloaded ∨
    (run stage).terminal = .bounded
  verified : (run stage).outcome.Valid
  traceValid : CT9.Graph.ValidTrace (capability stage) (ct9Input stage)
    (run stage).trace
  total : ∃ result,
    result = run stage ∧ result.outcome.Valid ∧
      CT9.Graph.ValidTrace (capability stage) (ct9Input stage) result.trace
  exactLedger : (ct9Input stage).items.values.length =
    ((capability stage).labels.orderedValues.map fun labelValue ↦
      CT9.fibreCount (capability stage) (ct9Input stage) labelValue).sum
  exactInput : (ct9Input stage).items =
    (SurplusPairResponse.pairEnumeration (setup := setup)).toOrderedCollection
  freeRoute : ∀ pair : FreePair stage, pairRole stage pair.1 = .freeAnchor
  blockedRoute : ∀ pair : BlockedPair stage,
    pairRole stage pair.1 = .blocked
      (SurplusTokenRole.admittedKind
        (SurplusPairResponse.canonicalBlocker stage pair).value)
  freeHandoff : ∀ {token} (item : FreeAnchorMember stage token),
    ¬(SurplusPairResponse.blockerFamily stage).HasBlocker item.pair ∧
      item.pair.first = token
  blockedHandoff : ∀ pair : BlockedPair stage,
    (SurplusPairResponse.canonicalBlocker stage pair).value ∈
        ((SurplusPairResponse.localBlockerProfile stage).candidates pair.1).values ∧
      (SurplusPairResponse.localBlockerProfile stage).Blocks pair.1
        (SurplusPairResponse.canonicalBlocker stage pair).value ∧
      ∀ candidate ∈ (SurplusPairResponse.canonicalBlocker stage pair).before,
        ¬(SurplusPairResponse.localBlockerProfile stage).Blocks pair.1 candidate
  checkCount : checks stage = (pairs (setup := setup)).card *
    ((tokens (setup := setup)).card * 5)
  polynomialChecks : checks stage ≤
    5 * ctx.G.object.input.vertices.card ^ 6

noncomputable def verifiedStage : VerifiedStage stage where
  terminal := run_terminal_exhaustive stage
  verified := run_verified stage
  traceValid := run_traceValid stage
  total := run_total stage
  exactLedger := noOvercounting stage
  exactInput := input_items_eq_pair_schedule stage
  freeRoute := free_role stage
  blockedRoute := blocked_role stage
  freeHandoff := fun {_token} item ↦
    ⟨freeAnchorFibre_member_is_free stage item,
      freeAnchorFibre_member_first stage item⟩
  blockedHandoff := blocked_retains_canonical_blocker stage
  checkCount := checks_eq stage
  polynomialChecks := checks_le_five_mul_sixthPower stage

end StructuralExhaustion.Graph.SurplusPairTokenRouting
