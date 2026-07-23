import Hypostructure.PDE.Strategy

/-!
# PDE fast-track row chains

Rows are registered as Core pipelines.  The dependent type of `next` forces
the following row to consume the complete ledger stage produced by the
preceding row, so fast-track output cannot be detached or supplied in
advance by an application.
-/

namespace Hypostructure.PDE.FastTrack.Pipeline

universe uPrevious

open Hypostructure

structure TwoRows (Previous : Type uPrevious) where
  first : PDE.Strategy.Pipeline Previous
  next : (stage : Core.Residual.Ledger.Extension Previous
    (fun stage => Sigma (first.execution.Payload stage))) ->
    PDE.Strategy.Pipeline (Core.Residual.Ledger.Extension Previous
      (fun stage => Sigma (first.execution.Payload stage)))

def run {Previous : Type uPrevious}
    (chain : TwoRows Previous) (previous : Previous) :=
  PDE.Strategy.chainPipelines chain.first chain.next previous

def firstStage {Previous : Type uPrevious}
    (chain : TwoRows Previous) (previous : Previous) :=
  Core.Strategy.run chain.first.execution previous

def checks {Previous : Type uPrevious}
    (chain : TwoRows Previous) (previous : Previous) : Nat :=
  chain.first.checks previous +
    (chain.next (firstStage chain previous)).checks
      (firstStage chain previous)

def work {Previous : Type uPrevious}
    (chain : TwoRows Previous) (previous : Previous) : Nat :=
  chain.first.work previous +
    (chain.next (firstStage chain previous)).work
      (firstStage chain previous)

@[simp] theorem run_previous {Previous : Type uPrevious}
    (chain : TwoRows Previous) (previous : Previous) :
    (run chain previous).previous =
      Core.Strategy.run chain.first.execution previous :=
  rfl

end Hypostructure.PDE.FastTrack.Pipeline
