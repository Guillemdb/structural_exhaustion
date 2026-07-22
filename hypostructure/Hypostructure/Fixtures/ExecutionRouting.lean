import Hypostructure.Core.Closure
import Hypostructure.Core.Execution
import Hypostructure.Core.Metadata
import Hypostructure.Core.Routing

/-!
# Execution, routing, closure, and metadata fixture

This finite fixture exercises the generic substrate without defining an
application-specific transition result.
-/

namespace Hypostructure.Fixtures.ExecutionRouting

open Hypostructure.Core

/-- Stable toy residual used to verify literal ledger preservation. -/
structure ToyResidual where
  value : Nat

def initial : Residual.Ledger ToyResidual :=
  Residual.Ledger.initial ⟨7⟩

def observe : Residual.StageNode (Residual.Ledger ToyResidual)
    (fun _previous => Nat) :=
  Residual.StageNode.create fun previous => (Residual.residualOf previous).value

abbrev ObservedStage :=
  Residual.Ledger.Extension (Residual.Ledger ToyResidual) (fun _ => Nat)

def observed : ObservedStage :=
  observe.run initial

def executionSpec : Execution.Spec ObservedStage where
  Input := fun _ => PUnit
  Outcome := fun _ _ => Nat
  Trace := fun previous _ outcome => PLift (outcome = previous.added)
  Sound := fun previous _ outcome _trace => outcome = previous.added
  Exhaustive := fun previous _ outcome => outcome = previous.added

def executionCapability : Execution.Capability executionSpec where
  reference := fun previous _ =>
    ⟨⟨previous.added, ⟨rfl⟩⟩, 1⟩
  sound := by
    intro previous input
    rfl
  exhaustive := by
    intro previous input
    rfl
  work := PolynomialCheckBudget.constant (fun _ => 1) 1
  checks_eq := by
    intro previous input
    rfl

def edge : Routing.Edge :=
  ⟨.ct1, .ct2, "fixture-total"⟩

def routeProfile : Routing.Profile.{0, 0, 0, 0, 0, 0} ObservedStage where
  Target := executionSpec
  executor := executionCapability
  Seed := fun _ => PUnit
  Blocked := fun _ => Empty
  discover := fun _ => .enabled PUnit.unit
  targetInput := fun _ _ => PUnit.unit

def transition : Routing.Transition.{0, 0, 0, 0, 0, 0}
    edge ObservedStage :=
  Routing.Transition.register edge routeProfile

def routed : Routing.Stage.{0, 0, 0, 0, 0, 0} transition :=
  Routing.advance transition observed

def focusedRouteProfile :
    Routing.Profile.{0, 0, 0, 0, 0, 0} ObservedStage :=
  Routing.Profile.ofFocus
    (Residual.Focus.always ObservedStage)
    executionSpec
    executionCapability
    (fun _source => PUnit)
    (fun _source _active => PUnit.unit)
    (fun _source _seed => PUnit.unit)

def focusedTransition : Routing.Transition.{0, 0, 0, 0, 0, 0}
    edge ObservedStage :=
  Routing.Transition.register edge focusedRouteProfile

def focusedRouted : Routing.Stage.{0, 0, 0, 0, 0, 0}
    focusedTransition :=
  Routing.advance focusedTransition observed

/-- Routing consumes the exact full predecessor, not a copied local value. -/
theorem fullLedgerPreserved : routed.previous = observed :=
  Routing.advance_previous transition observed

/-- Stable residual identity survives execution and route extension. -/
theorem rootResidualPreserved :
    Residual.residualOf routed = Residual.residualOf observed :=
  Routing.advance_residual transition observed

/-- Provenance is generated from the registered edge. -/
theorem routeProvenance : routed.added.provenance.recorded = edge :=
  routed.added.provenance.exact_edge

theorem focusedRoutePreservesPredecessor :
    focusedRouted.previous = observed :=
  Routing.advance_previous focusedTransition observed

theorem focusedRouteEnabled :
    focusedRouted.added.discovery = Routing.Discovery.enabled PUnit.unit := by
  rfl

def rankDecrease : Routing.StrictRankDecrease 4 3 :=
  ⟨by decide⟩

theorem routeRankDecreases : 3 < 4 :=
  rankDecrease.decreases

def directClosure : Closure.Result (2 + 2 = 4) :=
  Closure.Result.direct (.certificate rfl)

theorem directClosureVerified : 2 + 2 = 4 :=
  directClosure.proof

abbrev toyProblem : Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => PUnit

def toyProgress : Progress toyProblem where
  Measure := Nat
  lt := (.<.)
  wellFounded := Nat.lt_wfRel.wf
  measure := id

def toyTarget (n : Nat) : Prop := n < 2

def minimalContext :
    MinimalCounterexampleContext toyProblem toyTarget toyProgress where
  toAvoidingContext := {
    toBranchContext := {
      G := 2
      baseline := trivial
      state := PUnit.unit
    }
    avoids := by simp [toyTarget]
  }
  minimal := by
    intro candidate smaller baseline
    exact smaller

/-- Any purported smaller avoiding candidate is closed by the registered
minimality kernel. -/
theorem minimalityClosure
    (candidate : AvoidingContext toyProblem toyTarget)
    (smaller : toyProgress.Smaller candidate.G minimalContext.G) : False :=
  let evidence : Closure.StrictProgressEvidence minimalContext :=
    ⟨candidate, smaller⟩
  (Closure.Result.strictProgress evidence : Closure.Result False).proof

def fixtureDeclaration : DeclarationRef :=
  ⟨"Hypostructure.Fixtures.ExecutionRouting", "routed"⟩

def fixtureMetadata :
    Metadata.DeclarationMetadata ObservedStage
      (Execution.PackedInput executionSpec) where
  declaration := fixtureDeclaration
  primitiveInputs := [
    ⟨⟨"Hypostructure.Fixtures.ExecutionRouting", "executionCapability"⟩,
      .decisionProcedure⟩
  ]
  inferredDependencies := [
    ⟨⟨"Hypostructure.Core.Residual.Query", "latest"⟩,
      .predecessorProjection⟩
  ]
  ledgerQueries := [{
    source := ⟨"Hypostructure.Core.Residual.Query", "latest"⟩
    Result := fun _ => Nat
    query := Residual.Query.latest
  }]
  frameworkSearch := [
    ⟨"Hypostructure.Core.Execution", "runReference"⟩
  ]
  generatedOutputs := [
    ⟨⟨"Hypostructure.Core.Routing", "advance"⟩, .transitionResult⟩
  ]
  genericTheorems := [
    ⟨"Hypostructure.Core.Execution", "run_sound"⟩,
    ⟨"Hypostructure.Core.Execution", "run_work_bounded"⟩
  ]
  closureMechanisms := [.direct, .strictProgress]
  workBound := executionCapability.work
  manualObligations := []

def fixtureMetadataComplete : Metadata.Complete fixtureMetadata :=
  ⟨rfl⟩

theorem metadataHasNoManualObligation
    (obligation : Metadata.ManualObligation) :
    Not (obligation ∈ fixtureMetadata.manualObligations) :=
  fixtureMetadataComplete.no_manual_obligation obligation

#print axioms fullLedgerPreserved
#print axioms rootResidualPreserved
#print axioms routeRankDecreases
#print axioms directClosureVerified
#print axioms minimalityClosure
#print axioms focusedRoutePreservesPredecessor
#print axioms focusedRouteEnabled
#print axioms metadataHasNoManualObligation

end Hypostructure.Fixtures.ExecutionRouting
