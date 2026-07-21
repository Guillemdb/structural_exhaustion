import Hypostructure.Core.Residual.Ledger

/-!
# Residual ledger stages

Nodes contribute one local proposition or one local data value.  Running a
node is the only bookkeeping operation: Core installs the contribution in a
dependent `Ledger.Extension`, whose `previous` field is the literal input
stage.
-/

namespace Hypostructure.Core.Residual

universe uResidual uPrevious uOutput

/-- A proposition node over one exact predecessor stage. -/
structure Node (Previous : Sort uPrevious) (Property : Previous -> Prop) where
  private mk ::
  prove : (previous : Previous) -> Property previous

namespace Node

/-- Register the sole mathematical theorem contributed by a proposition
node.  Ledger extension remains framework-owned. -/
def create {Previous : Sort uPrevious} {Property : Previous -> Prop}
    (prove : (previous : Previous) -> Property previous) :
    Node Previous Property :=
  .mk prove

/-- Execute a proposition node on its literal predecessor. -/
def run {Previous : Sort uPrevious} {Property : Previous -> Prop}
    (node : Node Previous Property) (previous : Previous) :
    Ledger.Extension Previous Property :=
  Ledger.extend previous (node.prove previous)

@[simp] theorem run_previous
    {Previous : Sort uPrevious} {Property : Previous -> Prop}
    (node : Node Previous Property) (previous : Previous) :
    (node.run previous).previous = previous :=
  rfl

@[simp] theorem run_added
    {Previous : Sort uPrevious} {Property : Previous -> Prop}
    (node : Node Previous Property) (previous : Previous) :
    (node.run previous).added = node.prove previous :=
  rfl

end Node

/-- A data-bearing node over one exact predecessor stage.  Its output type may
depend on the complete predecessor ledger. -/
structure StageNode (Previous : Sort uPrevious)
    (Output : Previous -> Sort uOutput) where
  private mk ::
  produce : (previous : Previous) -> Output previous

namespace StageNode

/-- Register the sole mathematical value contributed by a data-bearing node. -/
def create {Previous : Sort uPrevious} {Output : Previous -> Sort uOutput}
    (produce : (previous : Previous) -> Output previous) :
    StageNode Previous Output :=
  .mk produce

/-- Execute a data-bearing node on its literal predecessor. -/
def run {Previous : Sort uPrevious} {Output : Previous -> Sort uOutput}
    (node : StageNode Previous Output) (previous : Previous) :
    Ledger.Extension Previous Output :=
  Ledger.extend previous (node.produce previous)

@[simp] theorem run_previous
    {Previous : Sort uPrevious} {Output : Previous -> Sort uOutput}
    (node : StageNode Previous Output) (previous : Previous) :
    (node.run previous).previous = previous :=
  rfl

@[simp] theorem run_added
    {Previous : Sort uPrevious} {Output : Previous -> Sort uOutput}
    (node : StageNode Previous Output) (previous : Previous) :
    (node.run previous).added = node.produce previous :=
  rfl

@[simp] theorem run_residual
    {Previous : Sort uPrevious} {Output : Previous -> Sort uOutput}
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (node : StageNode Previous Output) (previous : Previous) :
    residualOf (node.run previous) = residualOf previous :=
  rfl

end StageNode

end Hypostructure.Core.Residual
