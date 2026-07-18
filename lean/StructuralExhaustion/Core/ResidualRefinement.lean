import StructuralExhaustion.Core.FiniteResidualLedger

namespace StructuralExhaustion.Core.ResidualRefinement

universe uOccurrence uResidual uTarget uInput

/-!
# Accumulating residual refinements

A branch keeps one stable residual carrier.  Every node proves only its new
property; the framework retains the residual and all earlier proofs.
-/

/-- The dependent proof bundle for an ordered list of residual properties. -/
inductive Proofs {Residual : Type uResidual} (residual : Residual) :
    List (Residual → Prop) → Type uResidual where
  | nil : Proofs residual []
  | cons {property properties} :
      property residual → Proofs residual properties →
        Proofs residual (property :: properties)

namespace Proofs

variable {Residual : Type uResidual} {residual : Residual}
variable {property : Residual → Prop} {properties : List (Residual → Prop)}

def head (proofs : Proofs residual (property :: properties)) :
    property residual := by
  cases proofs with
  | cons proof _ => exact proof

def tail (proofs : Proofs residual (property :: properties)) :
    Proofs residual properties := by
  cases proofs with
  | cons _ earlier => exact earlier

/-- A typed position of one property in an accumulated proof bundle. -/
inductive Member (wanted : Residual → Prop) :
    List (Residual → Prop) → Type uResidual where
  | here {rest} : Member wanted (wanted :: rest)
  | there {other rest} : Member wanted rest →
      Member wanted (other :: rest)

def get {wanted : Residual → Prop} {facts : List (Residual → Prop)}
    (proofs : Proofs residual facts) (member : Member wanted facts) :
    wanted residual := by
  induction member with
  | here => exact proofs.head
  | there member ih => exact ih proofs.tail

end Proofs

/-- One current branch residual with every property established so far. -/
structure State (Residual : Type uResidual)
    (facts : List (Residual → Prop)) where
  residual : Residual
  proofs : Proofs residual facts

namespace State

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

def initial (residual : Residual) : State Residual [] where
  residual := residual
  proofs := .nil

/-- Add exactly one new proved property while retaining all earlier facts. -/
def add (state : State Residual facts) (property : Residual → Prop)
    (proof : property state.residual) :
    State Residual (property :: facts) where
  residual := state.residual
  proofs := .cons proof state.proofs

@[simp] theorem add_residual (state : State Residual facts)
    (property : Residual → Prop) (proof : property state.residual) :
    (state.add property proof).residual = state.residual :=
  rfl

def latest {property : Residual → Prop}
    (state : State Residual (property :: facts)) :
    property state.residual :=
  state.proofs.head

def earlier {property : Residual → Prop}
    (state : State Residual (property :: facts)) : State Residual facts where
  residual := state.residual
  proofs := state.proofs.tail

def get {property : Residual → Prop}
    (state : State Residual facts)
    (member : Proofs.Member property facts) : property state.residual :=
  state.proofs.get member

/-- The complete contract of one ordinary proof node.  Application code
supplies only `prove`; state extension is framework-owned. -/
structure Node (property : Residual → Prop) where
  prove : (state : State Residual facts) → property state.residual

def Node.run {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    State Residual (property :: facts) :=
  state.add property (node.prove state)

@[simp] theorem Node.run_residual {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    (node.run state).residual = state.residual :=
  rfl

theorem Node.run_latest {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    (node.run state).latest = node.prove state :=
  rfl

/-- A manuscript dichotomy on the current residual.  Both outcomes retain the
identical carrier and complete incoming fact bundle; the node supplies only
the exhaustive mathematical disjunction. -/
structure DecisionNode (yes no : Residual → Prop) where
  yesDecidable : (state : State Residual facts) →
    Decidable (yes state.residual)
  no_of_not_yes : (state : State Residual facts) →
    ¬ yes state.residual → no state.residual

inductive DecisionResult (state : State Residual facts)
    (yes no : Residual → Prop) where
  | yesBranch : State Residual (yes :: facts) →
      DecisionResult state yes no
  | noBranch : State Residual (no :: facts) →
      DecisionResult state yes no

def DecisionNode.run {yes no : Residual → Prop}
    (node : DecisionNode (facts := facts) yes no)
    (state : State Residual facts) : DecisionResult state yes no :=
  match node.yesDecidable state with
  | .isTrue proof => .yesBranch (state.add yes proof)
  | .isFalse proof => .noBranch (state.add no (node.no_of_not_yes state proof))

/-- The only explicit work required when the manuscript really changes the
residual carrier: construct the target residual and transport the facts that
the target branch is allowed to consume. -/
structure Route (Target : Type uTarget)
    (targetFacts : List (Target → Prop)) where
  targetResidual : State Residual facts → Target
  targetProofs : (state : State Residual facts) →
    Proofs (targetResidual state) targetFacts

def route {Target : Type uTarget} {targetFacts : List (Target → Prop)}
    (state : State Residual facts)
    (adapter : Route (facts := facts) Target targetFacts) :
    State Target targetFacts where
  residual := adapter.targetResidual state
  proofs := adapter.targetProofs state

end State

/-- An occurrence-indexed family of current residual states. -/
structure Ledger (Residual : Type uResidual)
    (facts : List (Residual → Prop)) where
  residuals : FiniteResidualLedger.Ledger.{uOccurrence, uResidual} Residual
  proofs : ∀ occurrence, Proofs (residuals.event occurrence) facts

namespace Ledger

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

noncomputable def initial
    (residuals : FiniteResidualLedger.Ledger.{uOccurrence, uResidual}
      Residual) : Ledger.{uOccurrence, uResidual} Residual [] where
  residuals := residuals
  proofs := fun _ => .nil

/-- A graph- or application-owned producer.  The framework maps it over the
exact input occurrence schedule and installs its first theorem as the first
accumulated fact. -/
structure Producer (Input : Type uInput) (property : Residual → Prop) where
  emit : Input → Residual
  prove : ∀ input, property (emit input)

/-- Start a refinement ledger from an exact producer schedule.  This is the
initial `ledger.add(theorem)` operation: occurrence identity is inherited from
the input schedule and the producer supplies only its local theorem. -/
noncomputable def produce {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Residual := Residual) Input property) :
    Ledger.{uOccurrence, uResidual} Residual [property] where
  residuals := inputs.map producer.emit
  proofs := fun occurrence => .cons (producer.prove (inputs.event occurrence)) .nil

@[simp] theorem produce_residual {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Residual := Residual) Input property)
    (occurrence : inputs.Occurrence) :
    (produce inputs producer).residuals.event occurrence =
      producer.emit (inputs.event occurrence) :=
  rfl

def state (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (occurrence : ledger.residuals.Occurrence) : State Residual facts where
  residual := ledger.residuals.event occurrence
  proofs := ledger.proofs occurrence

/-- Ordered residual values for compatibility with an older list-indexed
consumer.  This is a view of the occurrence ledger, never an independently
authored list. -/
noncomputable def events
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts) : List Residual :=
  ledger.residuals.entries.map ledger.residuals.event

theorem event_mem_events
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (occurrence : ledger.residuals.Occurrence) :
    ledger.residuals.event occurrence ∈ ledger.events :=
  List.mem_map_of_mem (ledger.residuals.occurrence_mem occurrence)

/-- Any named position in the accumulated fact schema is automatically
available to every value read from the compatibility list. -/
theorem fact_of_mem_events
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    {property : Residual → Prop} (position : Proofs.Member property facts)
    {residual : Residual} (member : residual ∈ ledger.events) :
    property residual := by
  rcases List.mem_map.mp member with ⟨occurrence, _occurrenceMem, rfl⟩
  exact (ledger.proofs occurrence).get position

/-- Add one occurrence-local theorem to the whole ledger.  This is the direct
Lean `ledger.add` surface: the caller proves only the new property from the
current occurrence state; the framework accumulates everything else. -/
noncomputable def add {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual) :
    Ledger.{uOccurrence, uResidual} Residual (property :: facts) where
  residuals := ledger.residuals
  proofs := fun occurrence =>
    .cons (prove occurrence) (ledger.proofs occurrence)

@[simp] theorem add_residuals {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual) :
    (ledger.add prove).residuals = ledger.residuals :=
  rfl

theorem add_latest {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual)
    (occurrence : ledger.residuals.Occurrence) :
    ((ledger.add prove).state occurrence).latest = prove occurrence :=
  rfl

/-- Run one proof node over every actual occurrence.  The finite universe,
event identity, and every earlier property are retained definitionally. -/
noncomputable def refine {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property) :
    Ledger.{uOccurrence, uResidual} Residual (property :: facts) where
  residuals := ledger.residuals
  proofs := fun occurrence =>
    .cons (node.prove (ledger.state occurrence)) (ledger.proofs occurrence)

@[simp] theorem refine_residuals {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property) :
    (ledger.refine node).residuals = ledger.residuals :=
  rfl

theorem refine_latest {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property)
    (occurrence : ledger.residuals.Occurrence) :
    ((ledger.refine node).state occurrence).latest =
      node.prove (ledger.state occurrence) :=
  rfl

/-- Compose two branches already carrying the same accumulated fact schema.
The sum tag preserves literal occurrence identity, and no proof field is
reconstructed by application code. -/
noncomputable def append
    (left right : Ledger.{uOccurrence, uResidual} Residual facts) :
    Ledger.{uOccurrence, uResidual} Residual facts where
  residuals := left.residuals.append right.residuals
  proofs
    | .inl occurrence => left.proofs occurrence
    | .inr occurrence => right.proofs occurrence

/-- Restrict to an explicitly decidable family of existing occurrences while
retaining every accumulated fact. -/
noncomputable def restrict
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (keep : ledger.residuals.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    Ledger.{uOccurrence, uResidual} Residual facts where
  residuals := ledger.residuals.restrict keep keepDecidable
  proofs := fun occurrence => ledger.proofs occurrence.1

/-- Route every occurrence through one explicit carrier-changing adapter.
Occurrence identity and enumeration remain unchanged. -/
noncomputable def route {Target : Type uTarget}
    {targetFacts : List (Target → Prop)}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (adapter : State.Route (facts := facts) Target targetFacts) :
    Ledger.{uOccurrence, uTarget} Target targetFacts where
  residuals := {
    Occurrence := ledger.residuals.Occurrence
    occurrences := ledger.residuals.occurrences
    event := fun occurrence =>
      adapter.targetResidual (ledger.state occurrence) }
  proofs := by
    intro occurrence
    exact adapter.targetProofs (ledger.state occurrence)

end Ledger

end StructuralExhaustion.Core.ResidualRefinement
