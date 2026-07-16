import StructuralExhaustion.Graph.SurplusHomogeneousPattern
import StructuralExhaustion.Graph.SurplusRoutingGerm

namespace StructuralExhaustion.Graph.SurplusPatternGermAudit

open StructuralExhaustion

universe u

/-!
# Exact germ audit of a homogeneous overloaded surplus fibre

This module is the reusable geometric consumer immediately after the
classwise overload and matching--star extraction.  It scans only the literal
matching or star returned by `SurplusHomogeneousPattern`; for every retained
pair it executes the predecessor blocker split, constructs the rooted BFS
closure, and records the exact comparison of the two selected endpoint germs.

No semantic conclusion is attached to a prefix, cubic, or high-incidence
comparison here.  Those conclusions require separate consumers.  Keeping the
exact comparison in the result prevents a later application from silently
assuming the desired bottleneck alternative.
-/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (activation : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev Token := SurplusCapacityTokenRouting.Token (ctx := ctx) (setup := setup)

noncomputable abbrev Routed (windowSize remainderSize primitiveSize : Nat) :=
  SurplusClasswiseOverload.RoutedOverload activation
    windowSize remainderSize primitiveSize

noncomputable abbrev HomogeneousAudit
    (windowSize remainderSize primitiveSize : Nat)
    (routed : Routed activation windowSize remainderSize primitiveSize) :=
  SurplusHomogeneousPattern.Audit activation
    windowSize remainderSize primitiveSize routed

/-- The literal list selected by the greedy matching--star stage. -/
noncomputable def patternPairs
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    List (Pair (setup := setup)) :=
  match audit with
  | .window _ stage =>
      match stage.pattern with
      | .matching result => result.pairs
      | .star result => result.pairs
  | .remainder _ stage =>
      match stage.pattern with
      | .matching result => result.pairs
      | .star result => result.pairs
  | .primitive _ stage =>
      match stage.pattern with
      | .matching result => result.pairs
      | .star result => result.pairs

/-- The selected list has exactly the threshold belonging to its routed token
class. -/
theorem patternPairs_length
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    (patternPairs activation audit).length =
      match audit with
      | .window _ _ => windowSize
      | .remainder _ _ => remainderSize
      | .primitive _ _ => primitiveSize := by
  cases audit with
  | window route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.exactSize
      | star result => simpa [patternPairs, patternEq] using result.exactSize
  | remainder route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.exactSize
      | star result => simpa [patternPairs, patternEq] using result.exactSize
  | primitive route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.exactSize
      | star result => simpa [patternPairs, patternEq] using result.exactSize

/-- No pair is synthesized by the geometric stage: the selected pattern is a
sublist of the exact overloaded token--role fibre. -/
theorem patternPairs_sublist
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    (patternPairs activation audit).Sublist
      (SurplusHomogeneousPattern.fibreSource activation
        windowSize remainderSize primitiveSize routed.overload).values := by
  cases audit with
  | window route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.sublist
      | star result => simpa [patternPairs, patternEq] using result.sublist
  | remainder route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.sublist
      | star result => simpa [patternPairs, patternEq] using result.sublist
  | primitive route stage =>
      cases patternEq : stage.pattern with
      | matching result => simpa [patternPairs, patternEq] using result.sublist
      | star result => simpa [patternPairs, patternEq] using result.sublist

theorem patternPairs_nodup
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (audit : HomogeneousAudit activation windowSize remainderSize primitiveSize routed) :
    (patternPairs activation audit).Nodup :=
  (SurplusHomogeneousPattern.fibreSource activation
    windowSize remainderSize primitiveSize routed.overload).nodup.sublist
      (patternPairs_sublist activation audit)

/-- Exact proof-carrying audit of one retained pair.  The only stored choice
is the already decidable blocked/free predecessor branch; all geometric data
below is a deterministic projection of this field. -/
structure PairAudit
    (token : Token (ctx := ctx) (setup := setup))
    (pair : Pair (setup := setup)) : Type u where
  branch : SurplusRoutingSupport.PairBranch activation pair

namespace PairAudit

/-- Coarse exhaustive tag of the exact tree-path comparison.  `parallel`
means that one selected rooted path is a prefix of the other; the two
divergent constructors retain their full proof payload in `comparison`. -/
inductive GeometryKind
  | parallel
  | divergeAtRoot
  | divergeAfterEdge
  deriving DecidableEq, Repr

def geometryKinds : List GeometryKind :=
  [.parallel, .divergeAtRoot, .divergeAfterEdge]

theorem mem_geometryKinds (kind : GeometryKind) : kind ∈ geometryKinds := by
  cases kind <;> simp [geometryKinds]

@[reducible] def geometryKindEnum : FinEnum GeometryKind :=
  FinEnum.ofList geometryKinds mem_geometryKinds

@[simp] theorem geometryKind_card : geometryKindEnum.card = 3 := by decide

noncomputable def comparison
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :=
  SurplusRoutingGerm.classifySelectedGerms activation token pair audit.branch

noncomputable def kind
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) : GeometryKind :=
  match comparison activation audit with
  | .leftPrefix .. => .parallel
  | .rightPrefix .. => .parallel
  | .divergeAtRoot .. => .divergeAtRoot
  | .divergeAfterEdge .. => .divergeAfterEdge

noncomputable def rootIncidence?
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :=
  SurplusRoutingGerm.classifySelectedRootIncidence?
    activation token pair audit.branch

noncomputable def afterEdgeIncidence?
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :=
  SurplusRoutingGerm.classifySelectedAfterEdgeIncidence?
    activation token pair audit.branch

theorem rootIncidence_isSome
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :
    (rootIncidence? activation audit).isSome =
      SurplusRoutingGerm.selectedGermsDivergeAtRoot
        activation token pair audit.branch :=
  SurplusRoutingGerm.classifySelectedRootIncidence?_isSome
    activation token pair audit.branch

theorem afterEdgeIncidence_isSome
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :
    (afterEdgeIncidence? activation audit).isSome =
      SurplusRoutingGerm.selectedGermsDivergeAfterEdge
        activation token pair audit.branch :=
  SurplusRoutingGerm.classifySelectedAfterEdgeIncidence?_isSome
    activation token pair audit.branch

/-- The tag is exhaustive and retains the underlying proof-carrying
comparison rather than replacing it by a Boolean observation. -/
theorem kind_cases
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair) :
    kind activation audit = .parallel ∨
      kind activation audit = .divergeAtRoot ∨
      kind activation audit = .divergeAfterEdge := by
  unfold kind
  generalize comparison activation audit = comparisonValue
  cases comparisonValue <;> simp

theorem rootIncidence_isSome_of_kind_eq
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair)
    (exact : kind activation audit = .divergeAtRoot) :
    (rootIncidence? activation audit).isSome = true := by
  rw [rootIncidence_isSome]
  unfold kind comparison at exact
  unfold SurplusRoutingGerm.selectedGermsDivergeAtRoot
  generalize SurplusRoutingGerm.classifySelectedGerms
    activation token pair audit.branch = comparisonValue at exact ⊢
  cases comparisonValue <;> simp at exact ⊢

theorem afterEdgeIncidence_isSome_of_kind_eq
    {token : Token (ctx := ctx) (setup := setup)}
    {pair : Pair (setup := setup)}
    (audit : PairAudit activation token pair)
    (exact : kind activation audit = .divergeAfterEdge) :
    (afterEdgeIncidence? activation audit).isSome = true := by
  rw [afterEdgeIncidence_isSome]
  unfold kind comparison at exact
  unfold SurplusRoutingGerm.selectedGermsDivergeAfterEdge
  generalize SurplusRoutingGerm.classifySelectedGerms
    activation token pair audit.branch = comparisonValue at exact ⊢
  cases comparisonValue <;> simp at exact ⊢

end PairAudit

/-- Complete geometric audit of the exact homogeneous pattern. -/
structure VerifiedStage
    {windowSize remainderSize primitiveSize : Nat}
    (routed : Routed activation windowSize remainderSize primitiveSize) : Type u where
  homogeneous : HomogeneousAudit activation
    windowSize remainderSize primitiveSize routed
  pairAudit : ∀ pair ∈ patternPairs activation homogeneous,
    PairAudit activation routed.overload.residual.label.1 pair

/-- Execute the blocker and germ classifier for every pair retained by the
homogeneous extractor. -/
noncomputable def verifiedStage
    {windowSize remainderSize primitiveSize : Nat}
    (routed : Routed activation windowSize remainderSize primitiveSize) :
    VerifiedStage activation routed where
  homogeneous := SurplusHomogeneousPattern.audit activation
    windowSize remainderSize primitiveSize routed
  pairAudit := fun pair _ =>
    ⟨SurplusRoutingSupport.classify activation pair⟩

/-- Per-pair closure and selected-germ construction remains polynomial in the
selected graph order. -/
theorem pairBudget_polynomial
    {windowSize remainderSize primitiveSize : Nat}
    {routed : Routed activation windowSize remainderSize primitiveSize}
    (stage : VerifiedStage activation routed)
    {pair : Pair (setup := setup)}
    (member : pair ∈ patternPairs activation stage.homogeneous) :
    SurplusRoutingGerm.zstarBudget routed.overload.residual.label.1 ≤
      1 + ctx.G.object.input.vertices.card *
          (ctx.G.object.input.vertices.card *
            (ctx.G.object.input.vertices.card + 1)) +
        ctx.G.object.input.vertices.card *
          (ctx.G.object.input.vertices.card + 1) +
        2 * ((ctx.G.object.input.vertices.card + 1) *
          (ctx.G.object.input.vertices.card + 1)) := by
  have _ := stage.pairAudit pair member
  exact SurplusRoutingGerm.zstarBudget_polynomial
    routed.overload.residual.label.1

end StructuralExhaustion.Graph.SurplusPatternGermAudit
