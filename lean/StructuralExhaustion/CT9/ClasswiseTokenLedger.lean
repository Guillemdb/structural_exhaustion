import StructuralExhaustion.CT9.TokenRoleLedger

namespace StructuralExhaustion.CT9.ClasswiseTokenLedger

open StructuralExhaustion

universe uAmbient uBranch uItem uToken uRole uClass

/-!
# Exact classwise token capacities

This profile refines an already authored finite item schedule by a token and a
role.  Each token has one finite class, and the caller supplies one local
capacity for every class.  The exact CT9 label capacity is therefore the
capacity of the token class; no aggregate or ambient estimate is stored in the
profile.

The coupled decision is deliberately asymmetric.  If total capacity is below
the item count, CT9 executes and returns its canonical overloaded fibre.  On
the other side it retains the literal total-capacity inequality.  The latter
does not claim that every individual fibre is bounded.
-/

structure Profile (P : Core.Problem.{uAmbient, uBranch}) where
  Item : Type uItem
  Token : Type uToken
  Role : Type uRole
  Class : Type uClass
  tokens : FinEnum Token
  roles : FinEnum Role
  classOf : Token → Class
  token : Item → Token
  role : Item → Role
  classCapacity : Class → Nat

namespace Profile

variable {P : Core.Problem.{uAmbient, uBranch}}
    (profile : Profile.{uAmbient, uBranch, uItem, uToken, uRole, uClass} P)

@[implicit_reducible]
def labels : FinEnum (profile.Token × profile.Role) := by
  letI : FinEnum profile.Token := profile.tokens
  letI : FinEnum profile.Role := profile.roles
  exact inferInstance

def assign (item : profile.Item) : profile.Token × profile.Role :=
  (profile.token item, profile.role item)

def labelCapacity (label : profile.Token × profile.Role) : Nat :=
  profile.classCapacity (profile.classOf label.1)

def capability : CT9.Capability P :=
  CT9.ExactLedger.capability P profile.Item
    (profile.Token × profile.Role) profile.labels profile.assign
    profile.labelCapacity

def input (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) : CT9.Input profile.capability :=
  CT9.ExactLedger.input context items

def run (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) :=
  CT9.run profile.capability (profile.input context items)

def totalCapacity : Nat := CT9.totalCapacity profile.capability

/-- Positive side of the coupled test.  The residual is the actual first
overloaded token--role fibre returned by CT9. -/
structure Overload (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) : Type _ where
  tooMany : profile.totalCapacity < items.values.length
  terminal : (profile.run context items).terminal = .overloaded
  trace : (profile.run context items).trace =
    [.entry, .partition, .overload, .overloadedTerminal]
  residual : CT9.OverloadResidual profile.capability (profile.input context items)
  residual_eq : residual = CT9.ExecutionResult.overloadResidual_of_terminal_eq
    profile.capability (profile.input context items)
    (profile.run context items) terminal
  verified : (profile.run context items).outcome.Valid
  traceValid : CT9.Graph.ValidTrace profile.capability (profile.input context items)
    (profile.run context items).trace
  total : ∃ result, result = profile.run context items ∧
    result.outcome.Valid ∧
    CT9.Graph.ValidTrace profile.capability (profile.input context items)
      result.trace

namespace Overload

variable {profile}

/-- Semantic form of the selected CT9 overload, stated directly in the
authored token-class capacity. -/
theorem classCapacity_lt_fibreCount
    {context : Core.BranchContext P}
    {items : Core.OrderedCollection profile.Item}
    (overload : profile.Overload context items) :
    profile.classCapacity (profile.classOf overload.residual.label.1) <
      CT9.fibreCount profile.capability (profile.input context items)
        overload.residual.label :=
  overload.residual.overloaded

/-- Duplicate-free item collection of the selected overloaded fibre. -/
noncomputable def fibreItems
    {context : Core.BranchContext P}
    {items : Core.OrderedCollection profile.Item}
    (overload : profile.Overload context items) :
    Core.OrderedCollection profile.Item where
  values := CT9.fibre profile.capability (profile.input context items)
    overload.residual.label
  nodup := items.nodup.filter _
  decEq := by
    letI : FinEnum profile.Token := profile.tokens
    letI : FinEnum profile.Role := profile.roles
    exact items.decEq

theorem classCapacity_lt_fibreItems_length
    {context : Core.BranchContext P}
    {items : Core.OrderedCollection profile.Item}
    (overload : profile.Overload context items) :
    profile.classCapacity (profile.classOf overload.residual.label.1) <
      overload.fibreItems.values.length :=
  overload.residual.overloaded

end Overload

/-- Negative side of the coupled test.  This is an exact aggregate statement,
not an unproved pointwise cap. -/
structure WithinCapacity (items : Core.OrderedCollection profile.Item) : Prop where
  bounded : items.values.length ≤ profile.totalCapacity

inductive Decision (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) : Type _ where
  | overload (result : profile.Overload context items)
  | withinCapacity (result : profile.WithinCapacity items)

noncomputable def decide (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) :
    profile.Decision context items := by
  by_cases tooMany : profile.totalCapacity < items.values.length
  · let terminal := CT9.run_terminal_overloaded_of_totalCapacity_lt_cardinality
      profile.capability (profile.input context items) tooMany
    exact .overload {
      tooMany := tooMany
      terminal := terminal
      trace := CT9.run_trace_overloaded_of_totalCapacity_lt_cardinality
        profile.capability (profile.input context items) tooMany
      residual := CT9.ExecutionResult.overloadResidual_of_terminal_eq
        profile.capability (profile.input context items)
        (profile.run context items) terminal
      residual_eq := rfl
      verified := CT9.run_verified profile.capability (profile.input context items)
      traceValid := CT9.run_trace_valid profile.capability (profile.input context items)
      total := ⟨profile.run context items, rfl,
        CT9.run_verified profile.capability (profile.input context items),
        CT9.run_trace_valid profile.capability (profile.input context items)⟩ }
  · exact .withinCapacity ⟨Nat.le_of_not_gt tooMany⟩

theorem exactPartition (context : Core.BranchContext P)
    (items : Core.OrderedCollection profile.Item) :
    items.values.length =
      (profile.labels.orderedValues.map fun label =>
        CT9.fibreCount profile.capability (profile.input context items) label).sum := by
  change (profile.input context items).items.values.length =
    ((profile.capability).labels.orderedValues.map fun label =>
      CT9.fibreCount profile.capability (profile.input context items) label).sum
  exact CT9.cardinality_eq_sum_fibreCount profile.capability
    (profile.input context items)

theorem totalCapacity_le (bound : Nat)
    (bounded : ∀ classValue, profile.classCapacity classValue ≤ bound) :
    profile.totalCapacity ≤ bound *
      (profile.tokens.card * profile.roles.card) := by
  unfold totalCapacity CT9.totalCapacity capability labelCapacity
  have pointwise : ∀ values : List (profile.Token × profile.Role),
      (values.map fun label => profile.classCapacity (profile.classOf label.1)).sum ≤
        (values.map fun _ => bound).sum := by
    intro values
    induction values with
    | nil => rfl
    | cons label tail inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (bounded _) inductionHypothesis
  calc
    (profile.labels.orderedValues.map fun label =>
        profile.classCapacity (profile.classOf label.1)).sum ≤
      (profile.labels.orderedValues.map fun _ => bound).sum :=
        pointwise profile.labels.orderedValues
    _ = bound * (profile.tokens.card * profile.roles.card) := by
      letI : FinEnum profile.Token := profile.tokens
      letI : FinEnum profile.Role := profile.roles
      simp [FinEnum.card_eq_fintypeCard, Nat.mul_comm]

def checks (items : Core.OrderedCollection profile.Item) : Nat :=
  items.values.length * profile.labels.card

theorem checks_eq (items : Core.OrderedCollection profile.Item) :
    profile.checks items = items.values.length *
      (profile.tokens.card * profile.roles.card) := by
  unfold checks
  congr 1
  letI : FinEnum profile.Token := profile.tokens
  letI : FinEnum profile.Role := profile.roles
  simp [FinEnum.card_eq_fintypeCard]

end Profile

end StructuralExhaustion.CT9.ClasswiseTokenLedger
