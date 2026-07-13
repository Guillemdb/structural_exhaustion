import Std

namespace StructuralExhaustion.Core.Routing

universe uResidual uContext uTrigger uSeed

/-!
Typed, residual-first routing primitives.

A producer emits only a semantic residual.  A route rule discovers a
consumer-specific seed and constructs the consumer trigger.  The rule's
dependent type fixes the target context and trigger contract; proof instances
provide only the explicitly declared target capability and context evidence
and, where the route contract requires it, a semantic discovery adapter.
-/

/-- The validated entry surface of a tactic. -/
structure TacticInterface where
  Context : Type uContext
  Trigger : Context → Type uTrigger

/-- A context-indexed trigger with its context hidden existentially in `Type`. -/
abbrev PackedTrigger (target : TacticInterface.{uContext, uTrigger}) :=
  (context : target.Context) × target.Trigger context

/-- Constructive capability discovery. -/
inductive Discovery (Seed : Type uSeed) where
  | enabled (seed : Seed)
  | disabled (reject : Seed → False)

namespace Discovery

def toOption {Seed : Type uSeed} : Discovery Seed → Option Seed
  | .enabled seed => some seed
  | .disabled _ => none

theorem enabled_sound {Seed : Type uSeed} (seed : Seed) :
    (Discovery.enabled seed).toOption = some seed :=
  rfl

theorem disabled_complete {Seed : Type uSeed} (reject : Seed → False) :
    (Discovery.disabled reject).toOption = none :=
  rfl

end Discovery

/-- A reusable route from one semantic residual kind to one target tactic. -/
structure RouteRule (Residual : Type uResidual)
    (target : TacticInterface.{uContext, uTrigger}) where
  routeId : String
  targetContext : Residual → target.Context
  Seed : Residual → Type uSeed
  discover : (residual : Residual) → Discovery (Seed residual)
  buildTrigger : (residual : Residual) →
    Seed residual → target.Trigger (targetContext residual)

/-- A generated route retains stable provenance and a well-typed target
trigger. -/
structure GeneratedRoute (target : TacticInterface.{uContext, uTrigger}) where
  routeId : String
  target : PackedTrigger target

/-- The result of applying a route rule to a particular residual. -/
inductive Attempt {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) where
  | enabled (seed : rule.Seed residual)
  | disabled (reject : rule.Seed residual → False)

namespace RouteRule

def attempt {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) : Attempt rule residual :=
  match rule.discover residual with
  | .enabled seed => .enabled seed
  | .disabled reject => .disabled reject

/-- Build the exact generated route from a discovered seed. -/
def generate {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) (seed : rule.Seed residual) : GeneratedRoute target where
  routeId := rule.routeId
  target := ⟨rule.targetContext residual, rule.buildTrigger residual seed⟩

/-- The result type of `buildTrigger` enforces target admission at the exact
context selected by the route. -/
def validTrigger {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) (seed : rule.Seed residual) :
    target.Trigger (rule.targetContext residual) :=
  rule.buildTrigger residual seed

theorem trigger_inhabited {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) (seed : rule.Seed residual) :
    Nonempty (target.Trigger (rule.targetContext residual)) :=
  ⟨rule.validTrigger residual seed⟩

theorem generated_provenance {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    (rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target)
    (residual : Residual) (seed : rule.Seed residual) :
    (rule.generate residual seed).routeId = rule.routeId :=
  rfl

end RouteRule

namespace Attempt

/-- Materialize an enabled attempt; disabled attempts retain their exact
seed-impossibility proof. -/
def generated? {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    {rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target}
    {residual : Residual} : Attempt rule residual → Option (GeneratedRoute target)
  | .enabled seed => some (rule.generate residual seed)
  | .disabled _ => none

theorem deterministic {Residual : Type uResidual}
    {target : TacticInterface.{uContext, uTrigger}}
    {rule : RouteRule.{uResidual, uContext, uTrigger, uSeed} Residual target}
    {residual : Residual} (left right : Attempt rule residual)
    (leftIsRun : left = rule.attempt residual)
    (rightIsRun : right = rule.attempt residual) : left = right :=
  leftIsRun.trans rightIsRun.symm

end Attempt

/-- Fixed-priority policy: select the first enabled route in registry order. -/
def selectFirst {target : TacticInterface.{uContext, uTrigger}}
    (routes : List (GeneratedRoute target)) : Option (GeneratedRoute target) :=
  routes.head?

theorem selectFirst_sound {target : TacticInterface.{uContext, uTrigger}}
    (routes : List (GeneratedRoute target)) {selected : GeneratedRoute target}
    (h : selectFirst routes = some selected) : selected ∈ routes := by
  cases routes with
  | nil => contradiction
  | cons head tail =>
      simp only [selectFirst, List.head?_cons] at h
      cases h
      exact List.mem_cons_self

theorem selectFirst_deterministic
    {target : TacticInterface.{uContext, uTrigger}}
    (routes : List (GeneratedRoute target))
    (left right : Option (GeneratedRoute target))
    (leftIsSelection : left = selectFirst routes)
    (rightIsSelection : right = selectFirst routes) : left = right :=
  leftIsSelection.trans rightIsSelection.symm

end StructuralExhaustion.Core.Routing
