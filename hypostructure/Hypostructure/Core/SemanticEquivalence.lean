import Hypostructure.Core.Problem

/-!
# Semantic equivalence

Representations may reconstruct an ambient object only up to a domain-provided
equivalence. Baseline and target transport are recorded independently so one
ambient problem can support several targets.
-/

namespace Hypostructure.Core

universe uAmbient uBranch

/-- Representation equivalence together with baseline invariance. -/
structure SemanticEquivalence (P : Problem.{uAmbient, uBranch}) where
  equivalent : P.Ambient -> P.Ambient -> Prop
  equivalence : Equivalence equivalent
  baseline_iff : equivalent G H -> (P.Baseline G ↔ P.Baseline H)

/-- Invariance of one external target under a chosen semantic equivalence. -/
structure TargetInvariant {P : Problem.{uAmbient, uBranch}}
    (E : SemanticEquivalence P) (Target : P.Ambient -> Prop) where
  target_iff : E.equivalent G H -> (Target G ↔ Target H)

namespace SemanticEquivalence

variable {P : Problem.{uAmbient, uBranch}}

/-- Every ambient object is semantically equivalent to itself. -/
@[refl] theorem refl (E : SemanticEquivalence P) (G : P.Ambient) :
    E.equivalent G G :=
  E.equivalence.refl G

/-- Semantic equivalence is symmetric. -/
@[symm] theorem symm (E : SemanticEquivalence P) {G H : P.Ambient}
    (equivalent : E.equivalent G H) : E.equivalent H G :=
  E.equivalence.symm equivalent

/-- Semantic equivalence is transitive. -/
@[trans] theorem trans (E : SemanticEquivalence P) {G H K : P.Ambient}
    (first : E.equivalent G H) (second : E.equivalent H K) :
    E.equivalent G K :=
  E.equivalence.trans first second

/-- Transport a baseline proof forward across semantic equivalence. -/
theorem transport_baseline (E : SemanticEquivalence P) {G H : P.Ambient}
    (equivalent : E.equivalent G H) (baseline : P.Baseline G) :
    P.Baseline H :=
  (E.baseline_iff equivalent).mp baseline

/-- Equality supplies canonical semantics for every problem. -/
def equality (P : Problem.{uAmbient, uBranch}) : SemanticEquivalence P where
  equivalent := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  baseline_iff := by
    intro G H equivalent
    cases equivalent
    rfl

@[simp] theorem equality_equivalent_iff (P : Problem.{uAmbient, uBranch})
    (G H : P.Ambient) :
    (SemanticEquivalence.equality P).equivalent G H ↔ G = H :=
  Iff.rfl

end SemanticEquivalence

namespace TargetInvariant

variable {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}
  {Target : P.Ambient -> Prop}

/-- Transport a target proof forward across semantic equivalence. -/
theorem transport (invariant : TargetInvariant E Target) {G H : P.Ambient}
    (equivalent : E.equivalent G H) (target : Target G) : Target H :=
  (invariant.target_iff equivalent).mp target

/-- Transport target avoidance forward across semantic equivalence. -/
theorem transport_not (invariant : TargetInvariant E Target) {G H : P.Ambient}
    (equivalent : E.equivalent G H) (avoids : Not (Target G)) :
    Not (Target H) := by
  intro targetH
  exact avoids ((invariant.target_iff equivalent).mpr targetH)

/-- Every target is invariant under equality semantics. -/
def equality (P : Problem.{uAmbient, uBranch}) (Target : P.Ambient -> Prop) :
    TargetInvariant (SemanticEquivalence.equality P) Target where
  target_iff := by
    intro G H equivalent
    cases equivalent
    rfl

end TargetInvariant

end Hypostructure.Core
