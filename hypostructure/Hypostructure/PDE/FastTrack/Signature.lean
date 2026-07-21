import Hypostructure.Core.Residual.Stage
import Hypostructure.PDE.Target

/-!
# Legal represented PDE signatures

This is row 1 of the PDE architecture.  The structure is an optional
capability over a `LocalModel`; no target or observable is added to the model
itself.  Registration uses the generic accumulated-ledger stage.
-/

namespace Hypostructure.PDE.FastTrack

universe u uPrevious

/-- Minimal legal represented signature for one external target. -/
structure Signature (M : LocalModel.{u})
    (Target : M.problem.Ambient -> Prop) where
  semantics : RepresentationSemantics M.problem
  observables : ObservableInterface M
  observableInvariant :
    ObservableInvariant M semantics observables
  targetInterface : TargetInterface M Target observables

namespace Signature

/-- The target-invariance theorem derived from the registered observables. -/
def targetInvariant {M : LocalModel.{u}}
    {Target : M.problem.Ambient -> Prop}
    (signature : Signature M Target) :
    Core.TargetInvariant signature.semantics Target :=
  signature.targetInterface.coreInvariant signature.observableInvariant

/-- Core node that installs a legal signature in the exact predecessor ledger. -/
def registrationNode {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {Target : M.problem.Ambient -> Prop}
    (signature : Signature M Target) :
    Core.Residual.StageNode Previous (fun _ => Signature M Target) :=
  Core.Residual.StageNode.create fun _ => signature

/-- Register row 1 without introducing a PDE-specific stage or output type. -/
def register {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {Target : M.problem.Ambient -> Prop}
    (signature : Signature M Target) (previous : Previous) :=
  (registrationNode signature).run previous

@[simp]
theorem register_previous {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {Target : M.problem.Ambient -> Prop}
    (signature : Signature M Target) (previous : Previous) :
    (register signature previous).previous = previous :=
  rfl

end Signature

end Hypostructure.PDE.FastTrack
