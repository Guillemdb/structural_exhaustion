namespace StructuralExhaustion.CT6.Interface

universe uA uB uM uT uO uW

/-!
The import-cycle-free entry contract for CT6.

Only data needed to validate an invocation lives here.  The executable
machine, its downstream consumers, and its node plans are deliberately kept
in `CT6.Types`.  This lets CT1 construct an exact CT6 input without importing
the CT6 implementation or any tactic to which CT6 may later route.
-/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Monitor : (G : Ambient) → BranchState G → Type uM
  Threshold : (G : Ambient) → BranchState G → Type uT
  FailureOrder : (G : Ambient) → BranchState G → Type uO
  FailureWitness : (G : Ambient) → BranchState G → Type uW
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
    Monitor G branch → Threshold G branch → FailureOrder G branch → Prop
  C1Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  monitor : F.Monitor G branch
  threshold : F.Threshold G branch
  failureOrder : F.FailureOrder G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.monitor input.threshold input.failureOrder

end StructuralExhaustion.CT6.Interface
