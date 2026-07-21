import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Residual.Stage

/-!
# Pointwise local-to-global closure

This module deliberately has no finite-enumeration premise.  A certificate is
pointwise over the exact sites owned by one ambient object; a domain profile
states how those local facts imply its global conclusion.  Finite CTs may
construct such a certificate from an explicit schedule, while analytic users
may prove it directly on an infinite family of windows.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uInterface uSite uAtom uContext uPrevious

namespace AtomContextAssembly

variable {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}

/-- A property of one exact atom/context pair. -/
abbrev LocalProperty
    (A : AtomContextAssembly P E) :=
  {interface : A.Interface} -> A.Atom interface -> A.Context interface -> Prop

/-- Pointwise evidence over every site belonging to one literal object. -/
structure PointwiseCertificate
    (A : AtomContextAssembly P E)
    (Local : A.LocalProperty) (object : P.Ambient) where
  localAt : forall site : A.Site object,
    Local (A.atom object site) (A.context object site)

/-- Domain theorem translating a pointwise atom/context property into a
global property.  Core owns application and ledger registration. -/
structure LocalToGlobalProfile
    (A : AtomContextAssembly P E)
    (Local : A.LocalProperty)
    (Global : P.Ambient -> Prop) where
  close : forall object, A.PointwiseCertificate Local object -> Global object

namespace LocalToGlobalProfile

/-- Apply a registered local-to-global theorem. -/
def run {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    (object : P.Ambient) (certificate : A.PointwiseCertificate Local object) :
    Global object :=
  profile.close object certificate

/-- Register local-to-global closure as a proposition node over the literal
predecessor ledger. -/
def node {A : AtomContextAssembly P E} {Local : A.LocalProperty}
    {Global : P.Ambient -> Prop}
    (profile : A.LocalToGlobalProfile Local Global)
    {Previous : Sort uPrevious}
    (object : Previous -> P.Ambient)
    (certificate : (previous : Previous) ->
      A.PointwiseCertificate Local (object previous)) :
    Residual.Node Previous (fun previous => Global (object previous)) :=
  Residual.Node.create fun previous =>
    profile.run (object previous) (certificate previous)

end LocalToGlobalProfile

end AtomContextAssembly

end Hypostructure.Core
