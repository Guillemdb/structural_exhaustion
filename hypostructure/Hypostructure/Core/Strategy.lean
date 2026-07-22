import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Ledger
import Hypostructure.Core.Budget.Dynamic

/-!
# Reusable strategy contracts

A strategy is a typed composition boundary above individual CTs.  Core owns
the terminal family, predecessor preservation, and composition shape.  The
domain supplies only schedules, observations, budgets, and semantic transfer
facts through the contract fields.
-/

namespace Hypostructure.Core.Strategy

universe uPrevious uTerminal uPayload uLeft uRight uItem uValue uCode

open Hypostructure.Core.Residual

/-- A strategy output indexed by its terminal.  The payload is dependent on
the literal predecessor and terminal, so branches cannot exchange data. -/
structure Contract (Previous : Type uPrevious) where
  Terminal : Type uTerminal
  Payload : Previous -> Terminal -> Type uPayload
  produce : (previous : Previous) -> Sigma (Payload previous)
  /-- Every predecessor receives an actual terminal payload. -/
  exhaustive : (previous : Previous) -> Nonempty (Sigma (Payload previous))

/-! ## Domain-neutral dichotomy

The two outcomes are deliberately unnamed.  An application may call them
Type A/Type B, fast/slow, or any other names, but Core only sees two
predecessor-indexed payloads.  This keeps classification and ledger routing in
the framework while leaving mathematical meaning to the application contract.
-/

inductive DichotomyTerminal where
  | left
  | right
  deriving DecidableEq, Repr

structure Dichotomy (Previous : Type uPrevious) where
  LeftPayload : Previous -> Type uLeft
  RightPayload : Previous -> Type uRight
  classify : (previous : Previous) ->
    Sum (LeftPayload previous) (RightPayload previous)

structure ClosedDichotomy (Previous : Type uPrevious) where
  LeftPayload : Previous -> Type uLeft
  RightPayload : Previous -> Type uRight
  classify : (previous : Previous) ->
    Sum (LeftPayload previous) (RightPayload previous)
  leftClosed : (previous : Previous) -> LeftPayload previous -> Prop
  rightClosed : (previous : Previous) -> RightPayload previous -> Prop
  leftProof : (previous : Previous) ->
    match classify previous with
    | Sum.inl payload => leftClosed previous payload
    | Sum.inr _ => True
  rightProof : (previous : Previous) ->
    match classify previous with
    | Sum.inl _ => True
    | Sum.inr payload => rightClosed previous payload

/-- A proposition carried as ordinary strategy data for finite routing. -/
abbrev ProofPayload (proposition : Prop) : Type := PLift proposition

def proofPayload (proof : proposition) : ProofPayload proposition :=
  ⟨proof⟩

def ClosedDichotomy.toDichotomy (strategy : ClosedDichotomy Previous) :
    Dichotomy Previous where
  LeftPayload := strategy.LeftPayload
  RightPayload := strategy.RightPayload
  classify := strategy.classify

theorem ClosedDichotomy.closed (strategy : ClosedDichotomy Previous)
    (previous : Previous) :
    match strategy.classify previous with
    | Sum.inl payload => strategy.leftClosed previous payload
    | Sum.inr payload => strategy.rightClosed previous payload := by
  cases h : strategy.classify previous with
  | inl payload =>
      simpa [h] using strategy.leftProof previous
  | inr payload =>
      simpa [h] using strategy.rightProof previous

/-! ## Routed continuation strategies

The branch continuation is a strategy, not an application-created payload.
Both continuations receive the literal predecessor stage selected by Core;
the branch witness is retained in the outer dependent sum. -/

abbrev RoutedLeft (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (previous : Previous) : Type _ :=
  Sigma (fun witness : split.LeftPayload previous =>
    Sigma ((left previous witness).Payload previous))

abbrev RoutedRight (split : Dichotomy Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) : Type _ :=
  Sigma (fun witness : split.RightPayload previous =>
    Sigma ((right previous witness).Payload previous))

/-/ The canonical dependent join produced by a routed dichotomy.  Keeping this
type alias public prevents applications from reconstructing branch sums or
copying branch witnesses by hand. -/
abbrev RoutedJoin (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) : Type _ :=
  Sum (RoutedLeft split left previous) (RoutedRight split right previous)

def runRouted
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) :
    Ledger.Extension Previous (RoutedJoin split left right) :=
  Ledger.extend previous (match split.classify previous with
    | Sum.inl witness =>
        Sum.inl ⟨witness, (left previous witness).produce previous⟩
    | Sum.inr witness =>
        Sum.inr ⟨witness, (right previous witness).produce previous⟩)

/-- Execute a dichotomy as one ledger extension.  The `Sum` is the terminal
tag and payload, so dependent branch witnesses are preserved without any
application-side routing. -/
def runDichotomy (strategy : Dichotomy Previous) (previous : Previous) :
    Residual.Ledger.Extension Previous
      (fun stage => Sum (strategy.LeftPayload stage)
        (strategy.RightPayload stage)) :=
  Residual.Ledger.extend previous (strategy.classify previous)

/-- The predecessor-preserving stage type produced by a dichotomy. -/
abbrev DichotomyStage (strategy : Dichotomy Previous) (previous : Previous) :=
  Residual.Ledger.Extension Previous
    (fun stage => Sum (strategy.LeftPayload stage)
      (strategy.RightPayload stage))

abbrev DichotomyPayload (strategy : Dichotomy Previous)
    (previous : Previous) : DichotomyTerminal -> Type (max uLeft uRight)
  | .left => strategy.LeftPayload previous
  | .right => strategy.RightPayload previous

noncomputable def dichotomyContract (strategy : Dichotomy Previous) :
    Contract Previous where
  Terminal := DichotomyTerminal
  Payload := DichotomyPayload strategy
  produce previous := match strategy.classify previous with
    | Sum.inl payload => ⟨.left, payload⟩
    | Sum.inr payload => ⟨.right, payload⟩
  exhaustive previous := ⟨match strategy.classify previous with
    | Sum.inl payload => ⟨.left, payload⟩
    | Sum.inr payload => ⟨.right, payload⟩⟩

/-- The one-extension execution owned by every strategy contract. -/
def run {Previous : Type uPrevious} (contract : Contract Previous)
    (previous : Previous) :
    Ledger.Extension Previous (fun stage => Sigma (contract.Payload stage)) :=
  Ledger.extend previous (contract.produce previous)

/-! ## Sequential composition

The next strategy receives the complete literal stage produced by the first
one.  This is the only composition primitive needed by applications: Core
owns predecessor retention and ledger growth, while the next contract may
inspect its predecessor-owned residual through the normal query API.
-/

def chain {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :
    Ledger.Extension (Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage)))
      (fun stage => Sigma ((next stage).Payload stage)) := by
  let middle := run first previous
  exact Ledger.extend middle ((next middle).produce middle)

/-- Public name for dependent strategy composition.  The second strategy is
indexed by the complete first result, so its queries cannot accidentally read
a detached predecessor or a copied payload. -/
def dependentChain {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :=
  chain first next previous

/-- A reusable finite strategy fragment with one dependent continuation.  A
longer program is formed by nesting `Sequence` in the continuation contract;
all predecessor stages remain literal ledger values. -/
/-
structure Sequence (Previous : Type uPrevious) where
  first : Contract.{uPrevious, uTerminal, uPayload} Previous
  next : (stage : Ledger.Extension Previous
    (fun stage => Sigma (first.Payload stage))) ->
    Contract.{uPrevious + 1, uTerminal, uPayload} (Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage)))

def Sequence.run {Previous : Type uPrevious} (sequence : Sequence Previous)
    (previous : Previous) :=
  dependentChain sequence.first sequence.next previous

@[simp] theorem Sequence.run_previous {Previous : Type uPrevious}
    (sequence : Sequence Previous)
    (previous : Previous) :
    (sequence.run previous).previous.previous = previous := rfl

abbrev Sequence.Payload {Previous : Type uPrevious}
    (sequence : Sequence Previous)
    (previous : Previous) : Type _ :=
  Sigma (fun firstResult : Sigma (sequence.first.Payload previous) =>
    Sigma ((sequence.next (Ledger.extend previous firstResult)).Payload
      (Ledger.extend previous firstResult)))

-- Reify a dependent sequence as one strategy contract.  The intermediate
result is retained in the final payload rather than copied into an
application-defined wrapper.
def Sequence.asContract {Previous : Type uPrevious}
    (sequence : Sequence Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ => sequence.Payload previous
  produce previous :=
    let firstStage := run sequence.first previous
    let secondStage := Ledger.extend firstStage
      ((sequence.next firstStage).produce firstStage)
    ⟨.unit, ⟨firstStage.added, secondStage.added⟩⟩
  exhaustive previous := by
    let firstStage := run sequence.first previous
    let secondStage := Ledger.extend firstStage
      ((sequence.next firstStage).produce firstStage)
    exact ⟨⟨.unit, ⟨firstStage.added, secondStage.added⟩⟩⟩

structure BranchSequences (Previous : Type uPrevious) where
  split : Dichotomy Previous
  left : (previous : Previous) -> split.LeftPayload previous -> Sequence Previous
  right : (previous : Previous) -> split.RightPayload previous -> Sequence Previous

def BranchSequences.run {Previous : Type uPrevious}
    (sequences : BranchSequences Previous)
    (previous : Previous) :=
  runRouted sequences.split
    (fun previous witness =>
      (sequences.left previous witness).asContract)
    (fun previous witness =>
      (sequences.right previous witness).asContract)
    previous
-/

/-! ## CT and pipeline facades

These structures carry no domain data.  They package already executable CT
contracts so Core can compose them, preserve their predecessor stages, and
aggregate their evidence uniformly for Graph and PDE applications.
-/

structure CTAdapter (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  checks : Previous -> Nat
  work : Previous -> Nat

/-- Adapt an already executable CT contract without changing its predecessor
or payload. -/
def CTAdapter.ofContract {Previous : Type uPrevious}
    (execution : Contract.{uPrevious, 0, uPrevious} Previous)
    (checks work : Previous -> Nat) : CTAdapter Previous where
  execution := execution
  checks := checks
  work := work

structure Pipeline (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  checks : Previous -> Nat
  work : Previous -> Nat
  closed : Previous -> Prop
  closed_proof : forall previous, closed previous

def CTAdapter.toPipeline (adapter : CTAdapter Previous)
    (closed : Previous -> Prop) (closed_proof : forall previous, closed previous) :
    Pipeline Previous where
  execution := adapter.execution
  checks := adapter.checks
  work := adapter.work
  closed := closed
  closed_proof := closed_proof

structure BranchPipelines (Previous : Type uPrevious) where
  split : Dichotomy Previous
  left : (previous : Previous) -> split.LeftPayload previous -> Pipeline Previous
  right : (previous : Previous) -> split.RightPayload previous -> Pipeline Previous

def BranchPipelines.run (pipelines : BranchPipelines Previous)
    (previous : Previous) :
    Ledger.Extension Previous
      (fun previous => Sum
        (RoutedLeft pipelines.split
          (fun previous witness => (pipelines.left previous witness).execution)
          previous)
        (RoutedRight pipelines.split
          (fun previous witness => (pipelines.right previous witness).execution)
          previous)) :=
  runRouted pipelines.split
    (fun previous witness => (pipelines.left previous witness).execution)
    (fun previous witness => (pipelines.right previous witness).execution)
    previous

@[simp] theorem runRouted_previous
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) :
    (runRouted split left right previous).previous = previous := rfl

@[simp] theorem runRouted_added
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) :
    (runRouted split left right previous).added =
      match split.classify previous with
      | Sum.inl witness => Sum.inl ⟨witness, (left previous witness).produce previous⟩
      | Sum.inr witness => Sum.inr ⟨witness, (right previous witness).produce previous⟩ := rfl

def pipelineChain {Previous : Type uPrevious}
    (first : Pipeline Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage))) -> Pipeline
        (Ledger.Extension Previous
          (fun stage => Sigma (first.execution.Payload stage))))
    (previous : Previous) :=
  chain first.execution
    (fun stage => (next stage).execution) previous

/-- Execute a branch continuation selected by Core.  The continuation may be
the first member of an arbitrarily long dependent sequence; subsequent steps
use `dependentChain` on the returned ledger stage. -/
def branchContinuation
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) :=
  runRouted split left right previous


@[simp] theorem pipelineChain_previous {Previous : Type uPrevious}
    (first : Pipeline Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage))) -> Pipeline
        (Ledger.Extension Previous
          (fun stage => Sigma (first.execution.Payload stage))))
    (previous : Previous) :
    (pipelineChain first next previous).previous =
      run first.execution previous := rfl

structure WorkEvidence (Previous : Type uPrevious) where
  checks : Previous -> Nat
  work : Previous -> Nat
  checks_nonnegative : forall previous, 0 <= checks previous
  work_nonnegative : forall previous, 0 <= work previous

/-! ## Public framework interfaces for composed CT programs -/

structure StrategyProjection (Root : Type uPrevious) (Value : Type uPayload) where
  read : Root -> Value

structure WorkProfile (Previous : Type uPrevious) where
  checks : Previous -> Nat
  work : Previous -> Nat

def WorkProfile.sequential (left right : WorkProfile Previous) :
    WorkProfile Previous where
  checks previous := left.checks previous + right.checks previous
  work previous := left.work previous + right.work previous

def WorkProfile.branch (left right : WorkProfile Previous) :
    WorkProfile Previous where
  checks previous := max (left.checks previous) (right.checks previous)
  work previous := max (left.work previous) (right.work previous)

inductive TerminalKind where
  | target
  | avoiding
  deriving DecidableEq, Repr

structure TerminalCertificate (Previous : Type uPrevious) where
  kind : TerminalKind
  target : Previous -> Prop
  avoiding : Previous -> Prop
  target_or_avoiding : forall previous,
    kind = .target ∧ target previous ∨ kind = .avoiding ∧ avoiding previous

theorem TerminalCertificate.closed (certificate : TerminalCertificate Previous)
    (previous : Previous) :
    match certificate.kind with
    | .target => certificate.target previous
    | .avoiding => certificate.avoiding previous := by
  rcases certificate.target_or_avoiding previous with h | h
  · simpa [h.1] using h.2
  · simpa [h.1] using h.2

structure ClosedPipeline (Previous : Type uPrevious) where
  pipeline : Pipeline Previous
  terminal : Previous -> TerminalCertificate Previous
  terminal_closed : forall previous,
    (terminal previous).kind = .target ∨ (terminal previous).kind = .avoiding

theorem ClosedPipeline.closed (closed : ClosedPipeline Previous)
    (previous : Previous) :
    match (closed.terminal previous).kind with
    | .target => (closed.terminal previous).target previous
    | .avoiding => (closed.terminal previous).avoiding previous :=
  (closed.terminal previous).closed previous

def normalizeStage {Previous : Type uPrevious} {Added : Previous -> Type uPayload}
    (stage : Ledger.Extension Previous Added) :
    Ledger.Extension Previous Added :=
  stage

/-- Public normalization boundary for an accumulated strategy stage. -/
abbrev NormalizedStage (Previous : Type uPrevious)
    (Added : Previous -> Type uPayload) := Ledger.Extension Previous Added

def normalizeContract {Previous : Type uPrevious}
    (contract : Contract Previous) := contract

def normalizeDichotomy {Previous : Type uPrevious}
    (dichotomy : Dichotomy Previous) := dichotomy

@[simp] theorem normalizeStage_eq {Previous : Type uPrevious}
    {Added : Previous -> Type uPayload}
    (stage : Ledger.Extension Previous Added) :
    normalizeStage stage = stage := rfl

def projectPrevious {Previous : Type uPrevious} {Value : Type uValue}
    {Added : Previous -> Type uPayload}
    (projection : Previous -> Value) :
    Ledger.Extension Previous Added -> Value :=
  fun stage => projection stage.previous

def projectChain {Previous : Type uPrevious} {Value : Type uValue}
    {First : Previous -> Type uPayload}
    {Second : Ledger.Extension Previous First -> Type uPayload}
    (projection : Previous -> Value) :
    Ledger.Extension (Ledger.Extension Previous First) Second -> Value :=
  fun stage => projection stage.previous.previous

@[simp] theorem projectChain_eq_previous {Previous : Type uPrevious}
    {Value : Type uValue} {First : Previous -> Type uPayload}
    {Second : Ledger.Extension Previous First -> Type uPayload}
    (projection : Previous -> Value)
    (stage : Ledger.Extension (Ledger.Extension Previous First) Second) :
    projectChain projection stage = projection stage.previous.previous := rfl

/-/ A branch join is represented by the routed ledger extension itself.  The
framework owns the join; applications only provide the two continuation
contracts to `runRouted`. -/
abbrev BranchJoin (Previous : Type uPrevious) (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (previous : Previous) : Type _ :=
  Ledger.Extension Previous (RoutedJoin split left right)

structure BranchWork (Previous : Type uPrevious) where
  left : Previous -> Nat
  right : Previous -> Nat

def BranchWork.total (profile : BranchWork Previous) (previous : Previous) : Nat :=
  profile.left previous + profile.right previous

structure DomainStrategy (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  projection : StrategyProjection Previous Previous
  work : WorkProfile Previous

def WorkEvidence.ofAdapter (adapter : CTAdapter Previous) :
    WorkEvidence Previous where
  checks := adapter.checks
  work := adapter.work
  checks_nonnegative := by intro; omega
  work_nonnegative := by intro; omega

@[simp] theorem chain_previous {Previous : Type uPrevious}
    (first : Contract Previous)
    (next : (stage : Ledger.Extension Previous
      (fun stage => Sigma (first.Payload stage))) ->
      Contract (Ledger.Extension Previous
        (fun stage => Sigma (first.Payload stage))))
    (previous : Previous) :
    (chain first next previous).previous = run first previous :=
  rfl

@[simp] theorem run_previous {Previous : Type uPrevious}
    (contract : Contract Previous) (previous : Previous) :
    (run contract previous).previous = previous := rfl

@[simp] theorem run_added {Previous : Type uPrevious}
    (contract : Contract Previous) (previous : Previous) :
    (run contract previous).added = contract.produce previous := rfl

/-- A strategy which only transports a previous terminal payload. -/
def map {Previous : Type uPrevious} (contract : Contract Previous)
    {NewTerminal : Type uTerminal} {NewPayload : Previous -> NewTerminal -> Type uPayload}
    (mapPayload : (previous : Previous) ->
      Sigma (contract.Payload previous) -> Sigma (NewPayload previous)) :
    Contract Previous where
  Terminal := NewTerminal
  Payload := NewPayload
  produce previous := mapPayload previous (contract.produce previous)
  exhaustive := fun previous =>
    ⟨mapPayload previous (contract.produce previous)⟩

/-! ## Common strategy pattern contracts -/

/-- An ordered finite witness scan.  The witness and its decision procedure
are domain inputs; first-hit semantics remain a Core contract. -/
structure OrderedWitnessScan (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  witness : (previous : Previous) -> Item previous -> Prop
  witnessDecidable : (previous : Previous) -> (item : Item previous) ->
    Decidable (witness previous item)
  Result : Previous -> Type uPayload
  run : (previous : Previous) -> Result previous
  exhaustive : (previous : Previous) -> (item : Item previous) ->
    item ∈ (schedule.read previous).values ->
      witness previous item ∨ ¬ witness previous item

/-- A finite response classifier over a predecessor-owned schedule. -/
structure ResponseClassifier (Previous : Type uPrevious) where
  Item : Previous -> Type uItem
  Response : Previous -> Type uValue
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  observe : (previous : Previous) -> Item previous -> Response previous
  Class : Previous -> Type uTerminal
  classify : (previous : Previous) -> Response previous -> Class previous
  exhaustive : (previous : Previous) -> (item : Item previous) ->
    ∃ cls : Class previous,
      classify previous (observe previous item) = cls

/-- A capacity ledger: every item has a class, a contribution, and a
residual-indexed capacity comparison.  The quantity can be graph charge or
PDE energy. -/
structure CapacityLedger (Previous : Type uPrevious) [Preorder Nat] where
  Item : Previous -> Type uItem
  Class : Previous -> Type uTerminal
  schedule : Query Previous (fun previous => Finite.Enumeration (Item previous))
  classify : (previous : Previous) -> Item previous -> Class previous
  contribution : (previous : Previous) -> Item previous -> Nat
  capacity : (previous : Previous) -> Class previous -> Nat
  totalWithin : (previous : Previous) -> (item : Item previous) ->
    contribution previous item <= capacity previous (classify previous item)

/-- A negative-budget localization contract. -/
structure SupportLocalization (Previous : Type uPrevious) where
  Cell : Previous -> Type uItem
  schedule : Query Previous (fun previous => Finite.Enumeration (Cell previous))
  localBudget : (previous : Previous) -> Cell previous -> Int
  selected : (previous : Previous) -> Cell previous
  selected_negative : (previous : Previous) ->
    localBudget previous (selected previous) < 0

/-- A target-avoiding continuation contract. -/
structure TargetAvoidingContinuation (Previous : Type uPrevious) where
  TargetCertificate : Previous -> Type uPayload
  AvoidingResidual : Previous -> Type uPayload
  target : (previous : Previous) -> TargetCertificate previous -> Prop
  avoiding : (previous : Previous) -> AvoidingResidual previous
  target_or_avoiding : (previous : Previous) ->
    (∃ certificate, target previous certificate) ∨
      Nonempty (AvoidingResidual previous)

/-- A finite rank/budget split contract. -/
structure RankBudgetSplit (Previous : Type uPrevious) where
  Rank : Previous -> Nat
  Budget : Previous -> Nat
  threshold : Previous -> Nat
  high : (previous : Previous) -> Prop
  low : (previous : Previous) -> Prop
  exhaustive : (previous : Previous) -> high previous ∨ low previous

/-- A closed-code exhaustion contract. -/
structure ClosedCodeExhaustion (Previous : Type uPrevious) where
  Code : Previous -> Type uCode
  schedule : Query Previous (fun previous => Finite.Enumeration (Code previous))
  targetCode : (previous : Previous) -> Code previous
  observedCode : (previous : Previous) -> Code previous -> Code previous
  closed : (previous : Previous) ->
    observedCode previous (targetCode previous) = targetCode previous

end Hypostructure.Core.Strategy
