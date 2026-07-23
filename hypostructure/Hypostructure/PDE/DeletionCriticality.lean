import Hypostructure.PDE.Deletion

/-!# PDE deletion criticality

The criticality statement is deliberately domain-neutral: every certified
baseline-preserving deletion is excluded at a minimal counterexample.  PDE
models may refine the subobject type to local pieces, windows, or packets.
-/

namespace Hypostructure.PDE.DeletionCriticality

universe uAmbient uBranch uMeasure uSubobject

theorem excludes
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : PDE.Deletion.Profile Target progress Subobject)
    (context : Core.MinimalCounterexampleContext P Target progress)
    (certificate : PDE.Deletion.Certificate profile context)
    (subobject : Subobject context.G) :
    Not (P.Baseline (profile.toAmbient subobject)) :=
  certificate.excludes subobject

end Hypostructure.PDE.DeletionCriticality
