import StructuralExhaustion.CT9.ExactLedger
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.CT9.TokenRoleLedger

open StructuralExhaustion

universe uAmbient uBranch uItem uToken uRole

/-!
# Exact token--role ledgers

This is the reusable CT9 profile for a finite item family charged by two
successive, deterministic coordinates: a capacity token and a finite role.
The framework scans the authored items once and partitions them by the product
label `(token, role)`.  Applications supply only the two total functions and
their explicit finite enumerations.
-/

@[implicit_reducible]
def labels {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role) : FinEnum (Token × Role) :=
  Core.Enumeration.prod tokens roles

def label {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (token : Item → Token) (role : Item → Role) (item : Item) : Token × Role :=
  (token item, role item)

def capability (P : Core.Problem.{uAmbient, uBranch})
    (Item : Type uItem) {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (capacity : Token → Role → Nat := fun _ _ ↦ 0) : CT9.Capability P :=
  CT9.ExactLedger.capability P Item (Token × Role) (labels tokens roles)
    (label token role) fun pair ↦ capacity pair.1 pair.2

def input {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    {tokens : FinEnum Token} {roles : FinEnum Role}
    {token : Item → Token} {role : Item → Role}
    {capacity : Token → Role → Nat}
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    CT9.Input (capability P Item tokens roles token role capacity) :=
  CT9.ExactLedger.input context items

/-- Every supplied item occurs in exactly one token--role fibre. -/
theorem noOvercounting {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    items.values.length =
      ((labels tokens roles).orderedValues.map fun labelValue ↦
        CT9.fibreCount
          (capability P Item tokens roles token role)
          (input (capacity := fun _ _ ↦ 0) context items) labelValue).sum := by
  exact CT9.ExactLedger.noOvercounting (labels tokens roles)
    (label token role) context items

/-- A uniform bound on every product fibre bounds the complete item family by
`bound * |Token| * |Role|`. -/
theorem bounded_total {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item)
    (bound : Nat)
    (bounded : ∀ tokenValue roleValue,
      CT9.fibreCount
        (capability P Item tokens roles token role)
        (input (capacity := fun _ _ ↦ 0) context items)
        (tokenValue, roleValue) ≤ bound) :
    items.values.length ≤ bound * (tokens.card * roles.card) := by
  have productBound : items.values.length ≤
      bound * (labels tokens roles).card :=
    CT9.ExactLedger.bounded_total (labels tokens roles) (label token role)
      context items bound fun pair ↦ bounded pair.1 pair.2
  simpa [labels, FinEnum.card_eq_fintypeCard, Nat.mul_assoc] using productBound

/-- Fibre membership exposes both authored coordinates literally. -/
theorem coordinates_of_mem_fibre
    {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    {tokens : FinEnum Token} {roles : FinEnum Role}
    {token : Item → Token} {role : Item → Role}
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item)
    {item : Item} {tokenValue : Token} {roleValue : Role}
    (member : item ∈ CT9.fibre
      (capability P Item tokens roles token role)
      (input (capacity := fun _ _ ↦ 0) context items)
      (tokenValue, roleValue)) :
    token item = tokenValue ∧ role item = roleValue := by
  letI : DecidableEq (Token × Role) := (labels tokens roles).decEq
  change item ∈ items.values.filter
    (fun current ↦ label token role current = (tokenValue, roleValue)) at member
  have equal := of_decide_eq_true (List.mem_filter.mp member).2
  exact Prod.ext_iff.mp equal

/-- The executable work is one product-label scan per supplied item. -/
def checks {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (items : Core.OrderedCollection Item) : Nat :=
  items.values.length * (tokens.card * roles.card)

theorem checks_eq {Item : Type uItem} {Token : Type uToken}
    {Role : Type uRole} (tokens : FinEnum Token) (roles : FinEnum Role)
    (items : Core.OrderedCollection Item) :
    checks tokens roles items =
      items.values.length * (tokens.card * roles.card) :=
  rfl

/-- Specialized exact work count when the authored items themselves are a
finite enumeration.  Keeping this reduction generic avoids unfolding a
problem-specific dependent item type during later polynomial proofs. -/
theorem checks_enumeration_eq {Item : Type uItem} {Token : Type uToken}
    {Role : Type uRole} (tokens : FinEnum Token) (roles : FinEnum Role)
    (items : FinEnum Item) :
    checks tokens roles items.toOrderedCollection =
      items.card * (tokens.card * roles.card) := by
  simp [checks, FinEnum.toOrderedCollection]

/-! ## Exact CT9 execution -/

/-- Execute CT9 on the exact product ledger with zero local capacities.  This
is the neutral execution contract for a pure partition stage: a nonempty
fibre is returned as an overload residual, while the empty item family is
certified bounded. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :=
  CT9.run
    (capability P Item tokens roles token role)
    (input (capacity := fun _ _ ↦ 0) context items)

/-- A pure token--role partition has zero aggregate capacity.  This fact is
owned by the reusable profile, so applications do not have to unfold the
product enumeration or the exact-ledger capability. -/
@[simp] theorem totalCapacity_eq_zero
    {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role) :
    CT9.totalCapacity (capability P Item tokens roles token role) = 0 := by
  simp [CT9.totalCapacity, capability, CT9.ExactLedger.capability]

/-- Every nonempty pure partition takes the exact overload terminal, since
all product-label capacities are zero. -/
theorem run_terminal_overloaded_of_items_nonempty
    {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item)
    (nonempty : items.values ≠ []) :
    (run tokens roles token role context items).terminal = .overloaded := by
  apply CT9.run_terminal_overloaded_of_totalCapacity_lt_cardinality
  rw [totalCapacity_eq_zero tokens roles token role]
  change 0 < items.values.length
  exact Nat.pos_of_ne_zero (by simpa using nonempty)

/-- Exact runner trace for a nonempty pure token--role partition. -/
theorem run_trace_overloaded_of_items_nonempty
    {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item)
    (nonempty : items.values ≠ []) :
    (run tokens roles token role context items).trace =
      [.entry, .partition, .overload, .overloadedTerminal] := by
  apply CT9.run_trace_overloaded_of_totalCapacity_lt_cardinality
  rw [totalCapacity_eq_zero tokens roles token role]
  change 0 < items.values.length
  exact Nat.pos_of_ne_zero (by simpa using nonempty)

theorem run_verified {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    (run tokens roles token role context items).outcome.Valid :=
  CT9.run_verified _ _

theorem run_traceValid {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    CT9.Graph.ValidTrace
      (capability P Item tokens roles token role)
      (input (capacity := fun _ _ ↦ 0) context items)
      (run tokens roles token role context items).trace :=
  CT9.run_trace_valid _ _

theorem run_terminal_exhaustive {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    (run tokens roles token role context items).terminal = .overloaded ∨
      (run tokens roles token role context items).terminal = .bounded :=
  CT9.outcome_exhaustive _ _ _

theorem run_total {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P) (items : Core.OrderedCollection Item) :
    ∃ result,
      result = run tokens roles token role context items ∧
      result.outcome.Valid ∧
      CT9.Graph.ValidTrace
        (capability P Item tokens roles token role)
        (input (capacity := fun _ _ ↦ 0) context items)
        result.trace :=
  ⟨run tokens roles token role context items, rfl,
    run_verified tokens roles token role context items,
    run_traceValid tokens roles token role context items⟩

/-- Complete reusable contract for an exact token--role partition. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P)
    (items : Core.OrderedCollection Item) : Prop where
  exactLedger : items.values.length =
    ((labels tokens roles).orderedValues.map fun labelValue ↦
      CT9.fibreCount
        (capability P Item tokens roles token role)
        (input (capacity := fun _ _ ↦ 0) context items)
        labelValue).sum
  terminal : (run tokens roles token role context items).terminal = .overloaded ∨
    (run tokens roles token role context items).terminal = .bounded
  verified : (run tokens roles token role context items).outcome.Valid
  traceValid : CT9.Graph.ValidTrace
    (capability P Item tokens roles token role)
    (input (capacity := fun _ _ ↦ 0) context items)
    (run tokens roles token role context items).trace
  total : ∃ result,
    result = run tokens roles token role context items ∧
    result.outcome.Valid ∧
    CT9.Graph.ValidTrace
      (capability P Item tokens roles token role)
      (input (capacity := fun _ _ ↦ 0) context items)
      result.trace
  checkCount : checks tokens roles items =
    items.values.length * (tokens.card * roles.card)

def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    {Item : Type uItem} {Token : Type uToken} {Role : Type uRole}
    (tokens : FinEnum Token) (roles : FinEnum Role)
    (token : Item → Token) (role : Item → Role)
    (context : Core.BranchContext P)
    (items : Core.OrderedCollection Item) :
    VerifiedStage tokens roles token role context items where
  exactLedger := noOvercounting tokens roles token role context items
  terminal := run_terminal_exhaustive tokens roles token role context items
  verified := run_verified tokens roles token role context items
  traceValid := run_traceValid tokens roles token role context items
  total := run_total tokens roles token role context items
  checkCount := checks_eq tokens roles items

end StructuralExhaustion.CT9.TokenRoleLedger
