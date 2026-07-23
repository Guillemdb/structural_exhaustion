import Hypostructure.Core.Strategy

/-!
# Declarative strategy DAGs

Applications assemble only registered strategy vertices. Core owns ledger
construction, dependent composition, branch routing, lowering, and execution.
The private constructors prevent applications from injecting contracts,
stages, outcomes, or compiled chains.
-/

namespace Hypostructure.Core.Strategy.Dag

open Hypostructure.Core.Residual

universe uRoot uStage uTerminal uPayload uAmbient uBranch uRunnerStage uRunnerPayload

/-- A strategy vertex admitted to a declarative DAG. -/
structure Registered (Previous : Type uStage) where
  private mk ::
  contract : Contract.{uStage, uTerminal, uPayload} Previous

namespace Registered

def orderedWitnessScan (strategy : OrderedWitnessScan Previous) :
    Registered Previous :=
  .mk strategy.asContract

def responseClassifier (strategy : ResponseClassifier Previous) :
    Registered Previous :=
  .mk strategy.asContract

def capacityLedger (strategy : CapacityLedger Previous) :
    Registered Previous :=
  .mk strategy.asContract

def supportLocalization (strategy : SupportLocalization Previous) :
    Registered Previous :=
  .mk strategy.asContract

noncomputable def targetAvoiding
    (strategy : TargetAvoidingContinuation Previous) : Registered Previous :=
  .mk strategy.asContract

noncomputable def rankBudget (strategy : RankBudgetSplit Previous) :
    Registered Previous :=
  .mk strategy.asContract

def closedCode (strategy : ClosedCodeExhaustion Previous) :
    Registered Previous :=
  .mk strategy.asContract

/-- Register a framework dichotomy together with every branch continuation. -/
def routed
    (split : Dichotomy Previous)
    (left : (previous : Previous) -> split.LeftPayload previous -> Registered Previous)
    (right : (previous : Previous) -> split.RightPayload previous -> Registered Previous) :
    Registered Previous :=
  .mk {
    Terminal := PUnit
    Payload := fun previous _ => RoutedJoin split
      (fun previous witness => (left previous witness).contract)
      (fun previous witness => (right previous witness).contract)
      previous
    produce := fun previous =>
      ⟨PUnit.unit, match split.classify previous with
        | Sum.inl witness =>
            Sum.inl ⟨witness, (left previous witness).contract.produce previous⟩
        | Sum.inr witness =>
            Sum.inr ⟨witness, (right previous witness).contract.produce previous⟩⟩
    exhaustive := fun previous =>
      ⟨⟨PUnit.unit, match split.classify previous with
        | Sum.inl witness =>
            Sum.inl ⟨witness, (left previous witness).contract.produce previous⟩
        | Sum.inr witness =>
            Sum.inr ⟨witness, (right previous witness).contract.produce previous⟩⟩⟩
  }

end Registered

/-- A well-typed, acyclic strategy program rooted at one residual type. -/
structure Program (Root : Type uRoot) where
  private mk ::
  Stage : Type uStage
  [stageResidual : HasResidual Stage Root]
  run : Root -> Stage
  residual_preserved : forall root, residualOf (run root) = root

instance (program : Program Root) : HasResidual program.Stage Root :=
  program.stageResidual

def Program.root : Program Root where
  Stage := Ledger Root
  run := Ledger.initial
  residual_preserved := by intro; rfl

def Program.then (program : Program Root)
    (vertex : Registered program.Stage) : Program Root where
  Stage := Ledger.Extension program.Stage
    (fun previous => Sigma (vertex.contract.Payload previous))
  run root := Strategy.run vertex.contract (program.run root)
  residual_preserved := program.residual_preserved

@[simp] theorem Program.then_previous (program : Program Root)
    (vertex : Registered program.Stage) (root : Root) :
    ((program.then vertex).run root).previous = program.run root :=
  rfl

/-- Public declarative DAG blueprint. -/
structure Blueprint (Root : Type uRoot) where
  private mk ::
  program : Program.{uRoot, uStage} Root

def Blueprint.root : Blueprint Root :=
  .mk Program.root

def Blueprint.add (dag : Blueprint Root)
    (vertex : Registered dag.program.Stage) : Blueprint Root :=
  .mk (dag.program.then vertex)

/-- Public proof DAG with inaccessible compiled representation. -/
structure Proof
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P) where
  private mk ::
  compiled : Chain.{uAmbient, uBranch, uRunnerStage, uRunnerPayload} P T

private def ofTargetProgram (program : TargetProgram P T) : Proof P T :=
  .mk program.toOutputStrategy

def compile (dag : Proof P T) : Chain P T :=
  dag.compiled

/-- Core finalization of an exact certified reduction. -/
private noncomputable def Program.finish
    (definition : Core.ProblemDefinition)
    (program : Program (ProblemInput definition.problem)) :
    Proof definition.problem definition.target :=
  .mk (OutputStrategy.unresolved definition.initialState program.run (by
      intro input
      rw [program.residual_preserved input]))

/-- Public application declaration. -/
structure ProblemDeclaration where
  private mk ::
  problem : Core.ProblemDefinition.{uAmbient, uBranch}
  dag : Proof.{uAmbient, uBranch, uRunnerStage, uRunnerPayload}
    problem.problem problem.target

/-- Sole application entrypoint. -/
noncomputable def ProblemDeclaration.ofDag
    (problem : Core.ProblemDefinition.{uAmbient, uBranch})
    (dag : Blueprint.{max uAmbient uBranch, uRunnerStage}
      (ProblemInput problem.problem)) :
    ProblemDeclaration.{uAmbient, uBranch, uRunnerStage, uRunnerStage} :=
  .mk problem (dag.program.finish problem)

private def ProblemDeclaration.compiled
    (declaration : ProblemDeclaration) : Strategy.CompiledDeclaration where
  problem := declaration.problem.problem
  target := declaration.problem.target
  strategy := compile declaration.dag

private def ProblemDeclaration.run (declaration : ProblemDeclaration) :=
  declaration.compiled.run

private noncomputable def ProblemDeclaration.diagnose
    (declaration : ProblemDeclaration) :=
  declaration.compiled.diagnose

/-- The unconditional target-or-exact-residual theorem produced by every DAG. -/
def ProblemDeclaration.Result (declaration : ProblemDeclaration) : Prop :=
  forall input,
    declaration.problem.target.Predicate
        (@residualOf (compile declaration.dag).Stage
          (ProblemInput declaration.problem.problem)
          (compile declaration.dag).stageResidual
          ((compile declaration.dag).run input).previous).object ∨
      Nonempty ((compile declaration.dag).Remaining
        ((compile declaration.dag).run input).previous)

theorem ProblemDeclaration.result
    (declaration : ProblemDeclaration) : declaration.Result := by
  intro input
  cases output : (compile declaration.dag).output input with
  | inl proof => exact Or.inl proof.down
  | inr residual => exact Or.inr ⟨residual⟩

abbrev ProblemDeclaration.TotalResidual
    (declaration : ProblemDeclaration) :=
  Sigma fun input : ProblemInput declaration.problem.problem =>
    Sigma fun residual : (compile declaration.dag).Remaining
        ((compile declaration.dag).run input).previous =>
      PLift ((compile declaration.dag).output input = Sum.inr residual)

abbrev ProblemDeclaration.CertifiedOutcome
    (declaration : ProblemDeclaration) :=
  Sum (PLift declaration.problem.target.Statement)
    declaration.TotalResidual

structure ProblemDeclaration.Report
    (declaration : ProblemDeclaration) where
  result : declaration.Result
  outcome : declaration.CertifiedOutcome

noncomputable def ProblemDeclaration.report
    (declaration : ProblemDeclaration) : declaration.Report where
  result := declaration.result
  outcome := declaration.diagnose

theorem ProblemDeclaration.unconditional
    (declaration : ProblemDeclaration)
    (target_case : forall input,
      ∃ proof : PLift (declaration.problem.target.Predicate
        (@residualOf (compile declaration.dag).Stage
          (ProblemInput declaration.problem.problem)
          (compile declaration.dag).stageResidual
          ((compile declaration.dag).run input).previous).object),
        (compile declaration.dag).output input = Sum.inl proof) :
    declaration.problem.target.Statement :=
  declaration.compiled.unconditional target_case

/-- Closure is exactly emptiness of the final residual family. -/
theorem ProblemDeclaration.unconditional_of_isEmpty
    (declaration : ProblemDeclaration)
    [empty : forall stage,
      IsEmpty ((compile declaration.dag).Remaining stage)] :
    declaration.problem.target.Statement :=
  (compile declaration.dag).unconditional_of_isEmpty

end Hypostructure.Core.Strategy.Dag
