import Hypostructure.Core.Minimality

/-!
# PDE minimality specialization

The PDE layer exports a specialization point onto the generic core minimality
machinery. This file is intentionally thin: PDE-specific code registers its
own subobject structure and then uses the core executor directly.
-/

namespace Hypostructure.PDE

open Core

universe uAmbient uBranch uMeasure uSubobject

abbrev SubobjectMinimalityProfile
    {P : Core.Problem.{uAmbient, uBranch}}
    (Target : P.Ambient → Prop)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (Subobject : P.Ambient → Type uSubobject) :=
  Core.Minimality.SubobjectMinimalityProfile
    (P := P) Target progress Subobject

abbrev NoSubobjectBaselineCertificate
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (ctx : Core.MinimalCounterexampleContext P Target progress) :=
  Core.Minimality.NoSubobjectBaselineCertificate (P := P) (Target := Target)
    (progress := progress) (Subobject := Subobject) profile ctx

def deriveNoSubobjectBaseline
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
    {Subobject : P.Ambient → Type uSubobject}
    (profile : SubobjectMinimalityProfile (P := P) Target progress Subobject)
    (ctx : Core.MinimalCounterexampleContext P Target progress) :
    NoSubobjectBaselineCertificate (P := P) (Target := Target)
      (progress := progress) (Subobject := Subobject) profile ctx :=
  Core.Minimality.deriveNoSubobjectBaseline (P := P) (Target := Target)
    (progress := progress) (Subobject := Subobject) profile ctx

end Hypostructure.PDE
