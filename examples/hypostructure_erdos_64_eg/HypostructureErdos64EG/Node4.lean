import Hypostructure.Graph.Progress
import Hypostructure.Core.Residual.Focus
import HypostructureErdos64EG.Node2

/-!
# Diagram node 4: lexicographically minimal counterexample

Node 4 opens Core's repeatable focus on node 2's exact counterexample
constructor. Core performs well-founded selection and leaves the terminal
node-3 sibling inactive without manufacturing a payload for it.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- Reusable graph progress instantiated by the EG problem registration. -/
abbrev EGProgress := Graph.lexicographicProgress Baseline BranchState

/-- Core-generated focus on node 2's counterexample constructor. -/
abbrev CounterexampleFocus :=
  Core.Residual.Focus.yes
    (Yes := IsCounterexample) (No := IsNotCounterexample)

/-- Exact counterexample proof selected by node 2. -/
def node2CounterexampleQuery :
    Core.Residual.Focus.ActiveQuery CounterexampleFocus
      (fun stage _active => IsCounterexample stage.previous) :=
  Core.Residual.Focus.yesProof

/-- Root data lifted through node 2's literal decision extension. -/
def node1ResidualAtNode2Query :
    Core.Residual.Query Node2Stage (fun _stage => InitialResidual.{u}) :=
  node1ResidualQuery.preserve

/-- Node 4 retrieves both inherited inputs through one active query. -/
def node4InputQuery :=
  node2CounterexampleQuery.and
    (Core.Residual.Focus.ActiveQuery.ofQuery node1ResidualAtNode2Query)

/-- Node 4's sole new payload on the focused branch. -/
abbrev Node4Output (_stage : Node2Stage.{u})
    (_active : CounterexampleFocus.Active _stage) :=
  Core.MinimalCounterexampleContext problem Target EGProgress

/-- Exact accumulated stage after node 4. -/
abbrev Node4Stage :=
  Core.Residual.Focus.Stage CounterexampleFocus Node4Output

/-- Execute minimal-counterexample selection on the exact focused branch. -/
noncomputable def node4 (previous : Node2Stage.{u}) : Node4Stage.{u} :=
  Core.Residual.Focus.run CounterexampleFocus previous fun active =>
    let inputs := node4InputQuery.read previous active
    Graph.selectLexicographicMinimal inputs.snd.object inputs.snd.baseline
      inputs.fst.2 (fun _current => ())

/-- Focus inherited by every downstream counterexample node. -/
abbrev Node4Focus :=
  Core.Residual.Focus.successor CounterexampleFocus Node4Output

/-- Typed ledger query for the selected minimal context. -/
def node4ContextQuery :
    Core.Residual.Focus.ActiveQuery Node4Focus
      (fun stage active => Node4Output stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

@[simp] theorem node4_previous (previous : Node2Stage.{u}) :
    (node4 previous).previous = previous :=
  rfl

end HypostructureErdos64EG
