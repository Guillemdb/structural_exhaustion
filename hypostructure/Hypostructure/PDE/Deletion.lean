import Hypostructure.PDE.Minimality

/-!# Generic PDE subobject deletion

PDE does not prescribe what a deletable piece is.  A model supplies the
subobject family and its reconstruction map; Core owns strict progress,
target transport, and the minimality contradiction.
-/

namespace Hypostructure.PDE.Deletion

universe uAmbient uBranch uMeasure uSubobject

abbrev Profile
    {P : Core.Problem.{uAmbient, uBranch}}
    (Target : P.Ambient → Prop)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (Subobject : P.Ambient → Type uSubobject) :=
  Core.Minimality.SubobjectMinimalityProfile
    (P := P) Target progress Subobject

abbrev Certificate
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : Profile Target progress Subobject)
    (context : Core.MinimalCounterexampleContext P Target progress) :=
  Core.Minimality.NoSubobjectBaselineCertificate profile context

def derive
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : Profile Target progress Subobject)
    (context : Core.MinimalCounterexampleContext P Target progress) :
    Certificate profile context :=
  Core.Minimality.deriveNoSubobjectBaseline profile context

end Hypostructure.PDE.Deletion
