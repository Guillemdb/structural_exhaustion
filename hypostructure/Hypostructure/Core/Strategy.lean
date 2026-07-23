import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Problem
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

/-! ## Problem initialization

The application boundary supplies only a Core problem and one theorem input.
Core packages that input as the first residual and creates the initial ledger;
all later strategies receive this exact stage through the ordinary composition
API.
-/

structure ProblemInput (P : Core.Problem) where
  object : P.Ambient
  baseline : P.Baseline object
  branchState : P.BranchState object

abbrev InitStage (P : Core.Problem) :=
  Ledger (ProblemInput P)

structure InitStrategy (P : Core.Problem) where
  run : ProblemInput P -> InitStage P

def InitStrategy.forProblem (P : Core.Problem) : InitStrategy P where
  run input := Ledger.initial input

@[simp] theorem InitStrategy.run_residual
    (P : Core.Problem) (input : ProblemInput P) :
    residualOf ((InitStrategy.forProblem P).run input) = input :=
  rfl

@[simp] theorem InitStrategy.run_object
    (P : Core.Problem) (input : ProblemInput P) :
    (residualOf ((InitStrategy.forProblem P).run input)).object = input.object :=
  rfl

/-! ## Target-closed strategy programs

This is the generic endpoint for a composed strategy.  The program owns its
execution stage and proves target realization from the literal residual carried
by that stage.  Core does not inspect or manufacture the stage payload; it
only exposes the target theorem bridge. -/

structure TargetProgram (P : Core.Problem) (T : Core.Target P) where
  Stage : Type uPrevious
  [stageResidual : HasResidual Stage (ProblemInput P)]
  branchState : forall object, P.BranchState object
  run : ProblemInput P -> Stage
  object_preserved : forall input,
    (residualOf (run input)).object = input.object
  target : forall input,
    T.Predicate (residualOf (run input)).object

theorem TargetProgram.statement
    (program : TargetProgram P T) : T.Statement := by
  apply T.target_to_statement
  intro object baseline
  let input : ProblemInput P :=
    { object := object
      baseline := baseline
      branchState := program.branchState object }
  simpa [program.object_preserved input] using program.target input

/-! ## Target reductions with an explicit unresolved residual

An unfinished strategy is still an unconditional reduction when every input
ends in either a certified target or a typed residual for a later strategy.
The residual is dependent on the exact final stage, so it cannot be detached
or replaced by application-side data. -/

structure TargetReduction (P : Core.Problem) (T : Core.Target P) where
  private mk ::
  Stage : Type uPrevious
  [stageResidual : HasResidual Stage (ProblemInput P)]
  Remaining : Stage -> Type uPayload
  branchState : forall object, P.BranchState object
  run : (input : ProblemInput P) -> Ledger.Extension Stage (fun stage =>
    Sum (PLift (T.Predicate (residualOf stage).object)) (Remaining stage))
  object_preserved : forall input,
    (residualOf (run input).previous).object = input.object

/-- Public output-side name for a strategy reduction.  Every execution exposes
either a certified target or the exact residual that still needs a consumer. -/
abbrev OutputStrategy (P : Core.Problem) (T : Core.Target P) :=
  TargetReduction P T

/-- A framework-owned executable strategy chain.  Its representation has a
private constructor, so application modules can only obtain a value through
Core strategy composition and terminal constructors. -/
abbrev Chain (P : Core.Problem) (T : Core.Target P) :=
  OutputStrategy P T

/-- Lift a target-closed program into the output protocol.  A closed program
has no remaining residual, so its output is always the target side and no
later continuation is evaluated. -/
def TargetProgram.toOutputStrategy
    (program : TargetProgram P T) : OutputStrategy P T where
  Stage := program.Stage
  stageResidual := program.stageResidual
  Remaining := fun _ => Empty
  branchState := program.branchState
  run input := Ledger.extend (program.run input) (Sum.inl ⟨program.target input⟩)
  object_preserved := program.object_preserved

def OutputStrategy.output
    (strategy : OutputStrategy P T) (input : ProblemInput P) :=
  (strategy.run input).added

/-- Core-owned unresolved endpoint.  This constructor cannot assert target
closure: it records the exact predecessor as the certified residual and fixes
the output alternative to `inr`. -/
def OutputStrategy.unresolved
    [HasResidual Stage (ProblemInput P)]
    (branchState : forall object, P.BranchState object)
    (runStage : ProblemInput P -> Stage)
    (object_preserved : forall input,
      (residualOf (runStage input)).object = input.object) : Chain P T where
  Stage := Stage
  Remaining := fun _ => PUnit
  branchState := branchState
  run input := Ledger.extend (runStage input) (Sum.inr PUnit.unit)
  object_preserved := object_preserved

theorem OutputStrategy.unconditional
    (strategy : OutputStrategy P T)
    (target_case : forall input,
      ∃ proof : PLift (T.Predicate
        (@residualOf strategy.Stage (ProblemInput P)
          strategy.stageResidual (strategy.run input).previous).object),
        strategy.output input = Sum.inl proof) :
    T.Statement := by
  apply T.target_to_statement
  intro object baseline
  let input : ProblemInput P :=
    { object := object
      baseline := baseline
      branchState := strategy.branchState object }
  rcases target_case input with ⟨proof, _equality⟩
  have certified := proof.down
  rw [strategy.object_preserved input] at certified
  simpa using certified

/-- Empty residual families close automatically.  The application supplies no
outcome classifier; Core eliminates the impossible residual alternative from
the final ledger entry. -/
theorem OutputStrategy.unconditional_of_isEmpty
    (strategy : OutputStrategy P T)
    [empty : forall stage, IsEmpty (strategy.Remaining stage)] :
    T.Statement := by
  apply strategy.unconditional
  intro input
  cases output : strategy.output input with
  | inl proof => exact ⟨proof, rfl⟩
  | inr residual => exact isEmptyElim residual

/-- Run a reduction to its earliest unconditional boundary.  If every input
reaches the target side, the result is the target theorem and no continuation
is needed.  Otherwise the result contains an input and the exact residual
produced by that run. -/
noncomputable def OutputStrategy.closeOrResidual
    (strategy : OutputStrategy P T) :
    Sum (PLift T.Statement)
      (Sigma fun input =>
        Sigma fun residual : strategy.Remaining (strategy.run input).previous =>
          PLift (strategy.output input = Sum.inr residual)) := by
  classical
  by_cases h : forall input,
      ∃ proof : PLift (T.Predicate
        (@residualOf strategy.Stage (ProblemInput P)
          strategy.stageResidual (strategy.run input).previous).object),
        strategy.output input = Sum.inl proof
  · exact Sum.inl ⟨OutputStrategy.unconditional strategy h⟩
  · push_neg at h
    let input := Classical.choose h
    have notTarget := Classical.choose_spec h
    cases output : strategy.output input with
    | inl proof =>
        exact False.elim (notTarget proof (by simpa [output]))
    | inr residual =>
        exact Sum.inr ⟨input, residual, ⟨output⟩⟩

/-- Runner-facing diagnostic projection.  This does not execute or transform
the strategy; it only inspects the already-defined output boundary to report
the earliest unconditional theorem or unresolved residual. -/
abbrev OutputDiagnostics (strategy : OutputStrategy P T) :=
  Sum (PLift T.Statement)
    (Sigma fun input =>
      Sigma fun residual : strategy.Remaining (strategy.run input).previous =>
        PLift (strategy.output input = Sum.inr residual))

noncomputable def OutputStrategy.diagnose
    (strategy : OutputStrategy P T) : OutputDiagnostics strategy :=
  strategy.closeOrResidual

/-! ## Hypostructure runner

The runner is the application-independent end-to-end boundary.  An
instantiation supplies one problem, its target contract, and one composed
strategy.  Execution remains the strategy's ordinary output; diagnostics are
an additional runner-side projection and never alter the strategy chain. -/

structure Hypostructure.{uAmbient, uBranch, uRunnerStage, uRunnerPayload} where
  Problem : Core.Problem.{uAmbient, uBranch}
  Target : Core.Target Problem
  strategy : Chain.{uAmbient, uBranch, uRunnerStage, uRunnerPayload}
    Problem Target

/-- Internal compiled declaration consumed by the low-level runner.  Public
applications use `Strategy.Dag.ProblemDeclaration`, whose DAG is lowered to
this representation exclusively by Core. -/
structure CompiledDeclaration.{uAmbient, uBranch, uRunnerStage, uRunnerPayload} where
  problem : Core.Problem.{uAmbient, uBranch}
  target : Core.Target problem
  strategy : Chain.{uAmbient, uBranch, uRunnerStage, uRunnerPayload}
    problem target

def Hypostructure.ofDeclaration
    (declaration : CompiledDeclaration) :
    Hypostructure where
  Problem := declaration.problem
  Target := declaration.target
  strategy := declaration.strategy

def CompiledDeclaration.hypostructure
    (declaration : CompiledDeclaration) :
    Hypostructure :=
  Hypostructure.ofDeclaration declaration

def CompiledDeclaration.run
    (declaration : CompiledDeclaration)
    (input : ProblemInput declaration.problem) :=
  declaration.strategy.output input

noncomputable def CompiledDeclaration.diagnose
    (declaration : CompiledDeclaration) :=
  declaration.strategy.diagnose

theorem CompiledDeclaration.unconditional
    (declaration : CompiledDeclaration)
    (target_case : forall input,
      ∃ proof : PLift (declaration.target.Predicate
        (@residualOf declaration.strategy.Stage
          (ProblemInput declaration.problem)
          declaration.strategy.stageResidual
          (declaration.strategy.run input).previous).object),
        declaration.strategy.output input = Sum.inl proof) :
    declaration.target.Statement :=
  OutputStrategy.unconditional declaration.strategy target_case

def Hypostructure.run (program : Hypostructure) :=
  program.strategy.output

noncomputable def Hypostructure.diagnose (program : Hypostructure) :=
  program.strategy.diagnose

theorem Hypostructure.unconditional
    (program : Hypostructure)
    (target_case : forall input,
      ∃ proof : PLift (program.Target.Predicate
        (@residualOf program.strategy.Stage
          (ProblemInput program.Problem)
          program.strategy.stageResidual
          (program.strategy.run input).previous).object),
        program.strategy.output input = Sum.inl proof) :
    program.Target.Statement :=
  OutputStrategy.unconditional program.strategy target_case

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

/- A reusable finite strategy fragment with one dependent continuation.  A
longer program is formed by nesting `Sequence` in the continuation contract;
all predecessor stages remain literal ledger values. -/
/-! Disabled draft sequence API.
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

/-- Continue a routed branch sequence from the complete joined stage.  The
next strategy is indexed by that stage, so it may inspect the selected branch
and all retained ledger entries through the normal residual queries. -/
def routedChain
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (next : (stage : Ledger.Extension Previous (RoutedJoin split left right)) ->
      Contract (Ledger.Extension Previous (RoutedJoin split left right)))
    (previous : Previous) :
    Ledger.Extension (Ledger.Extension Previous (RoutedJoin split left right))
      (fun stage => Sigma ((next stage).Payload stage)) := by
  let joined := runRouted split left right previous
  exact Ledger.extend joined ((next joined).produce joined)

@[simp] theorem routedChain_previous
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Contract Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Contract Previous)
    (next : (stage : Ledger.Extension Previous (RoutedJoin split left right)) ->
      Contract (Ledger.Extension Previous (RoutedJoin split left right)))
    (previous : Previous) :
    (routedChain split left right next previous).previous.previous = previous := rfl


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

/-- A routed execution together with its final terminal certificate.  The
certificate is indexed by the exact joined ledger stage, so closure cannot be
proved for a detached or reconstructed branch payload. -/
structure RoutedClosure (Previous : Type uPrevious) where
  split : Dichotomy.{uPrevious, uPrevious, uPrevious} Previous
  left : (previous : Previous) -> split.LeftPayload previous ->
    Contract.{uPrevious, 0, uPrevious} Previous
  right : (previous : Previous) -> split.RightPayload previous ->
    Contract.{uPrevious, 0, uPrevious} Previous
  terminal : TerminalCertificate (Ledger.Extension Previous
      (RoutedJoin split left right))

def RoutedClosure.run {Previous : Type uPrevious}
    (closure : RoutedClosure Previous)
    (previous : Previous) :=
  runRouted closure.split closure.left closure.right previous

theorem RoutedClosure.closed (closure : RoutedClosure Previous)
    (previous : Previous) :
    match closure.terminal.kind with
    | .target => closure.terminal.target
        (closure.run previous)
    | .avoiding => closure.terminal.avoiding
        (closure.run previous) :=
  closure.terminal.closed (closure.run previous)

structure BranchWork (Previous : Type uPrevious) where
  left : Previous -> Nat
  right : Previous -> Nat

def BranchWork.total (profile : BranchWork Previous) (previous : Previous) : Nat :=
  profile.left previous + profile.right previous

structure DomainStrategy (Previous : Type uPrevious) where
  execution : Contract.{uPrevious, 0, uPrevious} Previous
  projection : StrategyProjection Previous Previous
  work : WorkProfile Previous

/-! ## Generic success-or-residual strategy

Many domain rows have the same shape: a predecessor-owned predicate either
closes the row or leaves a typed residual for the next strategy.  The domain
supplies only the predicate, its decider, and residual construction. -/

inductive BinaryTerminal where
  | success
  | residual
  deriving DecidableEq, Repr

def binaryContract {Previous : Type uPrevious} {Residual : Previous -> Type uPayload}
    (Success : Previous -> Prop)
    (decideSuccess : (previous : Previous) -> Decidable (Success previous))
    (residual : (previous : Previous) -> Residual previous) :
    Contract.{uPrevious, 0, uPayload} Previous where
  Terminal := BinaryTerminal
  Payload := fun previous terminal => match terminal with
    | .success => ULift.{uPayload} (PLift (Success previous))
    | .residual => Residual previous
  produce previous :=
    @dite _ (Success previous) (decideSuccess previous)
      (fun proof => ⟨.success, ⟨⟨proof⟩⟩⟩)
      (fun _ => ⟨.residual, residual previous⟩)
  exhaustive previous := by
    exact @dite _ (Success previous) (decideSuccess previous)
      (fun proof => ⟨⟨.success, ⟨⟨proof⟩⟩⟩⟩)
      (fun _ => ⟨⟨.residual, residual previous⟩⟩)

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

/-! ## Executable strategy-pattern boundaries -/

def OrderedWitnessScan.asContract
    (strategy : OrderedWitnessScan Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ => strategy.Result previous
  produce previous := ⟨PUnit.unit, strategy.run previous⟩
  exhaustive previous := ⟨⟨PUnit.unit, strategy.run previous⟩⟩

namespace ResponseClassifier

abbrev Entry (strategy : ResponseClassifier Previous) (previous : Previous) :=
  Sigma fun item : strategy.Item previous =>
    Sigma fun cls : strategy.Class previous =>
      PLift (strategy.classify previous (strategy.observe previous item) = cls)

def entry (strategy : ResponseClassifier Previous) (previous : Previous)
    (item : strategy.Item previous) : strategy.Entry previous :=
  ⟨item, strategy.classify previous (strategy.observe previous item), ⟨rfl⟩⟩

def entries (strategy : ResponseClassifier Previous) (previous : Previous) :
    List (strategy.Entry previous) :=
  (strategy.schedule.read previous).values.map (strategy.entry previous)

def asContract (strategy : ResponseClassifier Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ => List (strategy.Entry previous)
  produce previous := ⟨PUnit.unit, strategy.entries previous⟩
  exhaustive previous := ⟨⟨PUnit.unit, strategy.entries previous⟩⟩

end ResponseClassifier

namespace CapacityLedger

abbrev Entry (strategy : CapacityLedger Previous) (previous : Previous) :=
  Sigma fun item : strategy.Item previous =>
    PLift (strategy.contribution previous item <=
      strategy.capacity previous (strategy.classify previous item))

def entry (strategy : CapacityLedger Previous) (previous : Previous)
    (item : strategy.Item previous) : strategy.Entry previous :=
  ⟨item, ⟨strategy.totalWithin previous item⟩⟩

def entries (strategy : CapacityLedger Previous) (previous : Previous) :
    List (strategy.Entry previous) :=
  (strategy.schedule.read previous).values.map (strategy.entry previous)

def asContract (strategy : CapacityLedger Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ => List (strategy.Entry previous)
  produce previous := ⟨PUnit.unit, strategy.entries previous⟩
  exhaustive previous := ⟨⟨PUnit.unit, strategy.entries previous⟩⟩

end CapacityLedger

def SupportLocalization.asContract
    (strategy : SupportLocalization Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ =>
    Sigma fun cell : strategy.Cell previous =>
      PLift (strategy.localBudget previous cell < 0)
  produce previous :=
    ⟨PUnit.unit, strategy.selected previous,
      ⟨strategy.selected_negative previous⟩⟩
  exhaustive previous :=
    ⟨⟨PUnit.unit, strategy.selected previous,
      ⟨strategy.selected_negative previous⟩⟩⟩

inductive TargetAvoidingTerminal where
  | target
  | avoiding

def TargetAvoidingContinuation.Payload
    (strategy : TargetAvoidingContinuation Previous)
    (previous : Previous) : TargetAvoidingTerminal -> Type _
  | .target => Sigma fun certificate : strategy.TargetCertificate previous =>
      PLift (strategy.target previous certificate)
  | .avoiding => strategy.AvoidingResidual previous

theorem TargetAvoidingContinuation.nonemptyPayload
    (strategy : TargetAvoidingContinuation Previous) (previous : Previous) :
    Nonempty (Sigma (strategy.Payload previous)) := by
  rcases strategy.target_or_avoiding previous with target | avoiding
  · rcases target with ⟨certificate, proof⟩
    exact ⟨⟨.target, certificate, ⟨proof⟩⟩⟩
  · rcases avoiding with ⟨residual⟩
    exact ⟨⟨.avoiding, residual⟩⟩

noncomputable def TargetAvoidingContinuation.asContract
    (strategy : TargetAvoidingContinuation Previous) : Contract Previous where
  Terminal := TargetAvoidingTerminal
  Payload := strategy.Payload
  produce previous := Classical.choice (strategy.nonemptyPayload previous)
  exhaustive previous := strategy.nonemptyPayload previous

inductive RankBudgetTerminal where
  | high
  | low

def RankBudgetSplit.Payload (strategy : RankBudgetSplit Previous)
    (previous : Previous) : RankBudgetTerminal -> Type
  | .high => PLift (strategy.high previous)
  | .low => PLift (strategy.low previous)

theorem RankBudgetSplit.nonemptyPayload
    (strategy : RankBudgetSplit Previous) (previous : Previous) :
    Nonempty (Sigma (strategy.Payload previous)) := by
  rcases strategy.exhaustive previous with high | low
  · exact ⟨⟨.high, ⟨high⟩⟩⟩
  · exact ⟨⟨.low, ⟨low⟩⟩⟩

noncomputable def RankBudgetSplit.asContract
    (strategy : RankBudgetSplit Previous) : Contract Previous where
  Terminal := RankBudgetTerminal
  Payload := strategy.Payload
  produce previous := Classical.choice (strategy.nonemptyPayload previous)
  exhaustive previous := strategy.nonemptyPayload previous

def ClosedCodeExhaustion.asContract
    (strategy : ClosedCodeExhaustion Previous) : Contract Previous where
  Terminal := PUnit
  Payload := fun previous _ =>
    PLift (strategy.observedCode previous (strategy.targetCode previous) =
      strategy.targetCode previous)
  produce previous := ⟨PUnit.unit, ⟨strategy.closed previous⟩⟩
  exhaustive previous := ⟨⟨PUnit.unit, ⟨strategy.closed previous⟩⟩⟩

end Hypostructure.Core.Strategy
