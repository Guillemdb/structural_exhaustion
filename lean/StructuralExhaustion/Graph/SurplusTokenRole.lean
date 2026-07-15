import StructuralExhaustion.Graph.SurplusPairBlocker

namespace StructuralExhaustion.Graph.SurplusTokenRole

open StructuralExhaustion

/-!
# Exact same-token role universe

The manuscript role is a blocker type together with one of the six disjoint
capacity-token subtypes.  Token class is determined by subtype, so the exact
uniform role universe has `6 * 6 = 36` elements.  This file contains only the
finite label algebra; token supports and assignments remain local inputs to
the later ledger.
-/

abbrev BlockerKind := SurplusPairBlocker.Kind

/-- Exactly the blocker kinds produced by the admitted structural scan.
Profile and target mismatches are raw quotient-audit exits and never enter the
canonical blocker ledger. -/
inductive AdmittedKind where
  | overlap
  | return
  | shoulder
  | chord
  deriving DecidableEq, Repr

def admittedKind {V : Type _} : SurplusPairBlocker.Candidate V → AdmittedKind
  | .sharedSupportVertex _ | .sharedSupportEdge _ => .overlap
  | .sharedReturnVertex _ | .sharedReturnEdge _ => .return
  | .sharedPortVertex _ _ _ => .shoulder
  | .suppressedChordFirst | .suppressedChordSecond => .chord

def admittedKinds : List AdmittedKind :=
  [.overlap, .return, .shoulder, .chord]

theorem mem_admittedKinds (kind : AdmittedKind) : kind ∈ admittedKinds := by
  cases kind <;> simp [admittedKinds]

@[reducible] def admittedKindEnum : FinEnum AdmittedKind :=
  FinEnum.ofList admittedKinds mem_admittedKinds

theorem admittedKind_card : admittedKindEnum.card = 4 := by decide

inductive TokenClass where
  | window
  | remainder
  | primitive
  deriving DecidableEq, Repr

inductive TokenSubtype where
  | windowRemainder
  | crossWindow
  | remainderSurplus
  | primitiveVertex
  | primitiveIncidence
  | primitivePort
  deriving DecidableEq, Repr

def TokenSubtype.tokenClass : TokenSubtype → TokenClass
  | .windowRemainder | .crossWindow => .window
  | .remainderSurplus => .remainder
  | .primitiveVertex | .primitiveIncidence | .primitivePort => .primitive

abbrev Role := BlockerKind × TokenSubtype
abbrev AdmittedRole := AdmittedKind × TokenSubtype

def blockerKinds : List BlockerKind :=
  [.overlap, .return, .shoulder, .profile, .target, .chord]

def tokenSubtypes : List TokenSubtype :=
  [.windowRemainder, .crossWindow, .remainderSurplus,
    .primitiveVertex, .primitiveIncidence, .primitivePort]

theorem mem_blockerKinds (kind : BlockerKind) : kind ∈ blockerKinds := by
  cases kind <;> simp [blockerKinds]

theorem mem_tokenSubtypes (subtype : TokenSubtype) :
    subtype ∈ tokenSubtypes := by
  cases subtype <;> simp [tokenSubtypes]

@[reducible] def blockerKindEnum : FinEnum BlockerKind :=
  FinEnum.ofList blockerKinds mem_blockerKinds

@[reducible] def tokenSubtypeEnum : FinEnum TokenSubtype :=
  FinEnum.ofList tokenSubtypes mem_tokenSubtypes

@[reducible] def roleEnum : FinEnum Role := by
  letI : FinEnum BlockerKind := blockerKindEnum
  letI : FinEnum TokenSubtype := tokenSubtypeEnum
  exact inferInstance

theorem blockerKind_card : blockerKindEnum.card = 6 := by decide

theorem tokenSubtype_card : tokenSubtypeEnum.card = 6 := by decide

theorem role_card : roleEnum.card = 36 := by decide

@[reducible] def admittedRoleEnum : FinEnum AdmittedRole := by
  letI : FinEnum AdmittedKind := admittedKindEnum
  letI : FinEnum TokenSubtype := tokenSubtypeEnum
  exact inferInstance

theorem admittedRole_card : admittedRoleEnum.card = 24 := by decide

/-- Intermediate role used by the total node `[130]` route.  A blocked pair
retains exactly its canonical blocker kind; its capacity-token subtype is
computed only by the downstream blocker ledger.  A blocker-free pair carries
the distinct `freeAnchor` role and is routed by its first selected surplus
port. -/
inductive PairRouteRole where
  | blocked (kind : AdmittedKind)
  | freeAnchor
  deriving DecidableEq, Repr

def pairRouteRoles : List PairRouteRole :=
  admittedKindEnum.orderedValues.map PairRouteRole.blocked ++ [.freeAnchor]

theorem mem_pairRouteRoles (role : PairRouteRole) : role ∈ pairRouteRoles := by
  cases role with
  | blocked blockerKind =>
      simp [pairRouteRoles, admittedKindEnum.mem_orderedValues]
  | freeAnchor => simp [pairRouteRoles]

@[reducible] def pairRouteRoleEnum : FinEnum PairRouteRole :=
  FinEnum.ofList pairRouteRoles mem_pairRouteRoles

theorem pairRouteRole_card : pairRouteRoleEnum.card = 5 := by decide

theorem blocked_ne_freeAnchor (kind : AdmittedKind) :
    PairRouteRole.blocked kind ≠ .freeAnchor := by
  simp

/-- Final role used after the blocked branch has computed its capacity-token
subtype.  It extends the manuscript's `6 × 6` blocked alphabet by the one
free-anchor role routed through primitive selected-port tokens. -/
inductive TotalRole where
  | blocked (role : AdmittedRole)
  | freeAnchor
  deriving DecidableEq, Repr

def totalRoles : List TotalRole :=
  admittedRoleEnum.orderedValues.map TotalRole.blocked ++ [.freeAnchor]

theorem mem_totalRoles (role : TotalRole) : role ∈ totalRoles := by
  cases role with
  | blocked blockedRole =>
      simp [totalRoles, admittedRoleEnum.mem_orderedValues]
  | freeAnchor => simp [totalRoles]

@[reducible] def totalRoleEnum : FinEnum TotalRole :=
  FinEnum.ofList totalRoles mem_totalRoles

theorem totalRole_card : totalRoleEnum.card = 25 := by decide

theorem total_blocked_ne_freeAnchor (role : AdmittedRole) :
    TotalRole.blocked role ≠ .freeAnchor := by
  simp

/-- The subtype partition has the exact manuscript class sizes `2+1+3`. -/
theorem subtype_class_counts :
    (tokenSubtypes.filter fun subtype => subtype.tokenClass = .window).length = 2 ∧
    (tokenSubtypes.filter fun subtype => subtype.tokenClass = .remainder).length = 1 ∧
    (tokenSubtypes.filter fun subtype => subtype.tokenClass = .primitive).length = 3 := by
  decide

end StructuralExhaustion.Graph.SurplusTokenRole
