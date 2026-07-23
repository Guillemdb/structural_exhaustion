import Hypostructure.Core.SemanticEquivalence
import Hypostructure.PDE.Model
import Hypostructure.PDE.Representation

/-!
# PDE representation invariance

PDE representatives may differ by pressure gauge, normalization, quotient,
or equality.  This module packages the public invariant surface corresponding
to Graph isomorphism invariance without imposing a specific analytic notion of
equivalence.
-/

namespace Hypostructure.PDE.Isomorphism

universe u

abbrev Equivalent (M : PDE.LocalModel.{u})
    (S : PDE.RepresentationSemantics M.problem) := S.equivalent

def Invariant (M : PDE.LocalModel.{u})
    (S : PDE.RepresentationSemantics M.problem)
    (Property : M.problem.Ambient -> Prop) : Prop :=
  forall {left right}, Equivalent M S left right ->
    (Property left ↔ Property right)

def transport {M : PDE.LocalModel.{u}}
    {S : PDE.RepresentationSemantics M.problem}
    {Property : M.problem.Ambient -> Prop}
    (invariant : Invariant M S Property)
    {left right : M.problem.Ambient}
    (equivalent : Equivalent M S left right) :
    Property left ↔ Property right :=
  invariant equivalent

end Hypostructure.PDE.Isomorphism
