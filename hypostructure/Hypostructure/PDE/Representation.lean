import Hypostructure.Core.SemanticEquivalence
import Hypostructure.PDE.Model

/-!
# PDE representation semantics
-/

namespace Hypostructure.PDE

universe u

/-- PDE-facing name for Core semantic equivalence. -/
abbrev RepresentationSemantics (P : Core.Problem.{u, u}) :=
  Core.SemanticEquivalence P

namespace RepresentationSemantics

/-- Literal equality is the default representation semantics. -/
def equality (P : Core.Problem.{u, u}) : RepresentationSemantics P :=
  Core.SemanticEquivalence.equality P

@[refl]
theorem refl {P : Core.Problem.{u, u}} (S : RepresentationSemantics P)
    (G : P.Ambient) : S.equivalent G G :=
  S.equivalence.refl G

@[symm]
theorem symm {P : Core.Problem.{u, u}} {S : RepresentationSemantics P}
    {G H : P.Ambient} (h : S.equivalent G H) : S.equivalent H G :=
  S.equivalence.symm h

@[trans]
theorem trans {P : Core.Problem.{u, u}} {S : RepresentationSemantics P}
    {G H K : P.Ambient} (hGH : S.equivalent G H)
    (hHK : S.equivalent H K) : S.equivalent G K :=
  S.equivalence.trans hGH hHK

end RepresentationSemantics

/-- PDE-facing name for Core target invariance. -/
abbrev TargetInvariant {P : Core.Problem.{u, u}}
    (S : RepresentationSemantics P) (Target : P.Ambient -> Prop) :=
  Core.TargetInvariant S Target

namespace TargetInvariant

/-- Transport a target proof across semantic equivalence. -/
theorem transport {P : Core.Problem.{u, u}} {S : RepresentationSemantics P}
    {Target : P.Ambient -> Prop} (I : TargetInvariant S Target)
    {G H : P.Ambient} (hGH : S.equivalent G H) (hG : Target G) : Target H :=
  (I.target_iff hGH).mp hG

end TargetInvariant

end Hypostructure.PDE
