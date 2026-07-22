import Hypostructure.Core.NormalForm.ClassClosure
import Hypostructure.Core.Residual.Focus
import Hypostructure.CT15.Execution
import Hypostructure.CT16.Execution
import Hypostructure.PDE.StructuralGradient

/-!
# PDE fast-track row 5: directed exhaustiveness

This is the bounded executable form of Definition 13.3, row 5, and
Theorems 4.2--4.7 of `PDEs/10_continuous_extension.ipynb`.

The executor runs only on an exact Core focus.  On that branch it performs
one CT15 generation.  Both finite full-rank terminals can imply a continuum
structural gap only through the registered analytic `FullRankToGap` bridge.
A rank drop continues to one CT16 generation; proper support is retained as
an impossible branch only when the registered alignment proves that fact.
The two whole-support CT16 terminals are aligned with one authoritative
`ClassClosure` generation.  CT16 never reimplements or repeats that quotient
scan.

The three semantic terminals are exactly:

* a positive structural gap, hence closed range and directed exhaustiveness;
* a target-complete zero boundary quotient with Core ledger propagation; or
* the exact first target-visible in-window boundary class, with positive
  capacity and nonzero target flux.

No regularized inverse is accepted as exact closure, and no finite-rank fact
is promoted to a continuum gap without the explicit analytic bridge.
-/

namespace Hypostructure.PDE.FastTrack.DirectedExhaustiveness

open Hypostructure.Core

universe uPrevious uPotential uCurrent uRankCoordinate uSupportCoordinate
  uCode uCarrier uQuotient uNextQuotient

variable {Previous : Type uPrevious}
variable {Potential : Type uPotential} {Current : Type uCurrent}
variable [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
variable [CompleteSpace Potential]
variable [NormedAddCommGroup Current] [InnerProductSpace Real Current]
variable [CompleteSpace Current]

/-- The exact focused predecessor passed temporarily to the shared CTs. -/
abbrev ActiveView (focus : Hypostructure.Core.Residual.Focus.Profile Previous) :=
  Hypostructure.Core.Residual.Focus.ActiveView focus

/-- The mandatory analytic bridge between CT15's two finite full-rank
terminals and a genuine continuum Poincare gap.  CT15 alone proves neither a
spectral gap nor closed range. -/
structure FullRankToGap
    (focus : Hypostructure.Core.Residual.Focus.Profile Previous)
    (gradient : Hypostructure.Core.Residual.Focus.ActiveQuery focus fun _previous _proof =>
      StructuralGradient Potential Current)
    (rankSpec : Hypostructure.CT15.Spec.{uPrevious, uRankCoordinate}
      (ActiveView focus))
    (rankCapability : Hypostructure.CT15.Capability rankSpec) where
  fromC4 : forall (view : ActiveView focus),
    Hypostructure.CT15.C4Output rankCapability view ->
      StructuralGradient.PositiveStructuralGap
        (gradient.read view.previous view.proof)
  fromFullRankLedger : forall (view : ActiveView focus),
    Hypostructure.CT15.FullRankLedgerOutput rankCapability view ->
      StructuralGradient.PositiveStructuralGap
        (gradient.read view.previous view.proof)

/-- Semantic alignment between the finite CT15/CT16 audit and the exact
boundary quotient executor.  A rank drop is the only CT15 branch admitted to
CT16.  Whole-support exact code means an exhaustive target-visibility miss;
whole-support mismatch means a target-visible class exists. -/
structure CodeClosureAlignment
    (focus : Hypostructure.Core.Residual.Focus.Profile Previous)
    (rankSpec : Hypostructure.CT15.Spec.{uPrevious, uRankCoordinate}
      (ActiveView focus))
    (rankCapability : Hypostructure.CT15.Capability rankSpec)
    (supportSpec : Hypostructure.CT16.Spec.{uPrevious, uSupportCoordinate,
      uCode} (ActiveView focus))
    (supportCapability : Hypostructure.CT16.Capability supportSpec)
    (closureProfile : Hypostructure.Core.NormalForm.ClassClosure.Profile.{uPrevious, uCarrier, uQuotient}
      (ActiveView focus)) : Prop where
  properSupportImpossible : forall (view : ActiveView focus),
    Hypostructure.CT15.RankDropOutput rankCapability view ->
    Hypostructure.CT16.ProperSupportOutput supportCapability view -> False
  exactCodeAvoids : forall (view : ActiveView focus),
    Hypostructure.CT15.RankDropOutput rankCapability view ->
    Hypostructure.CT16.ExactCodeOutput supportCapability view ->
      closureProfile.AvoidsTargetVisible view
  mismatchVisible : forall (view : ActiveView focus),
    Hypostructure.CT15.RankDropOutput rankCapability view ->
    Hypostructure.CT16.MismatchOutput supportCapability view ->
      closureProfile.HasTargetVisible view

/-- Minimal row-5 registration.  Every finite schedule is queried through the
temporary Core active view; the enclosing executor still extends the literal
focused predecessor. -/
structure Profile
    (Previous : Type uPrevious) (focus : Hypostructure.Core.Residual.Focus.Profile Previous)
    (Potential : Type uPotential) (Current : Type uCurrent)
    [NormedAddCommGroup Potential] [InnerProductSpace Real Potential]
    [CompleteSpace Potential]
    [NormedAddCommGroup Current] [InnerProductSpace Real Current]
    [CompleteSpace Current] where
  gradient : Hypostructure.Core.Residual.Focus.ActiveQuery focus fun _previous _proof =>
    StructuralGradient Potential Current
  closedRangeCriterion : Hypostructure.Core.Residual.Focus.ActiveQuery focus fun previous proof =>
    StructuralGradient.ClosedRangeCriterion (gradient.read previous proof)
  rankSpec : Hypostructure.CT15.Spec.{uPrevious, uRankCoordinate}
    (ActiveView focus)
  rankCapability : Hypostructure.CT15.Capability rankSpec
  supportSpec : Hypostructure.CT16.Spec.{uPrevious, uSupportCoordinate, uCode}
    (ActiveView focus)
  supportCapability : Hypostructure.CT16.Capability supportSpec
  closureProfile : Hypostructure.Core.NormalForm.ClassClosure.Profile.{uPrevious, uCarrier, uQuotient}
    (ActiveView focus)
  closureRegistration : Hypostructure.Core.NormalForm.ClassClosure.ExtensionRegistration.{uPrevious,
    uCarrier, uQuotient, uNextQuotient} closureProfile
  targetComplete : Hypostructure.Core.Residual.Focus.ActiveQuery focus
    fun _previous _proof =>
      Hypostructure.Core.NormalForm.ClassClosure.TargetComplete closureProfile
  InWindow : (view : ActiveView focus) -> closureProfile.Carrier -> Prop
  targetCapacity : (view : ActiveView focus) -> closureProfile.Carrier -> Real
  targetFlux : (view : ActiveView focus) -> closureProfile.Carrier -> Real
  inWindowOfVisible : forall (view : ActiveView focus)
    (carrier : closureProfile.Carrier),
    closureProfile.IsTargetVisible view carrier -> InWindow view carrier
  positiveCapacityOfVisible : forall (view : ActiveView focus)
    (carrier : closureProfile.Carrier),
    closureProfile.IsTargetVisible view carrier ->
      0 < targetCapacity view carrier
  nonzeroFluxOfVisible : forall (view : ActiveView focus)
    (carrier : closureProfile.Carrier),
    closureProfile.IsTargetVisible view carrier ->
      targetFlux view carrier ≠ 0
  fullRankToGap : Hypostructure.Core.Residual.Focus.ActiveQuery focus
    fun _previous _proof =>
      FullRankToGap focus gradient rankSpec rankCapability
  codeClosureAlignment : Hypostructure.Core.Residual.Focus.ActiveQuery focus
    fun _previous _proof =>
      CodeClosureAlignment focus rankSpec rankCapability supportSpec
        supportCapability closureProfile

/-- Exhaustive semantic terminals of the row-5 executor. -/
inductive Terminal where
  | positiveStructuralGap
  | zeroBoundaryQuotient
  | targetVisibleBoundary
  deriving DecidableEq, Repr

/-- Closed-range payload generated only after the mandatory analytic bridge. -/
structure PositiveGapOutput
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) where
  private mk ::
  gap : StructuralGradient.PositiveStructuralGap
    (profile.gradient.read view.previous view.proof)
  closedRange : StructuralGradient.ClosedRangeCertificate
    (profile.gradient.read view.previous view.proof)
  directed : StructuralGradient.DirectedExhaustivenessCertificate
    (profile.gradient.read view.previous view.proof)

/-- Target-complete closed terminal.  `boundaryZero` concerns every class of
the represented quotient, not merely the finite family inspected by Core. -/
structure ZeroBoundaryOutput
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) where
  private mk ::
  closure : Hypostructure.Core.NormalForm.ClassClosure.ZeroQuotientOutput profile.closureProfile
    profile.closureRegistration view
  boundaryZero : Hypostructure.Core.NormalForm.ClassClosure.BoundaryZero profile.closureProfile view

/-- Exact open boundary residual.  This payload deliberately stops before a
realization/nonpolarity theorem: in-window visibility, positive capacity, and
nonzero flux do not by themselves assert that the target is reached. -/
structure TargetVisibleBoundaryOutput
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) where
  private mk ::
  closure : Hypostructure.Core.NormalForm.ClassClosure.TargetVisibleOutput profile.closureProfile view
  inWindow : profile.InWindow view closure.residual.hit.value
  positiveCapacity : 0 < profile.targetCapacity view
    closure.residual.hit.value
  nonzeroFlux : profile.targetFlux view closure.residual.hit.value ≠ 0

/-- Constructor-sealed output-only result.  Optional CT16 and class-closure
evidence records the literal path: full-rank branches stop after CT15, while a
rank drop contains exactly one CT16 and one class-closure generation. -/
structure Generated
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) where
  private mk ::
  terminal : Terminal
  rank : Hypostructure.CT15.Routed profile.rankCapability view
  support : Option (Hypostructure.CT16.Generated profile.supportSpec
    profile.supportCapability view)
  classClosure : Option (Hypostructure.Core.NormalForm.ClassClosure.Generated profile.closureProfile
    profile.closureRegistration view)
  positiveGap : terminal = .positiveStructuralGap ->
    PositiveGapOutput profile view
  zeroBoundary : terminal = .zeroBoundaryQuotient ->
    ZeroBoundaryOutput profile view
  targetVisible : terminal = .targetVisibleBoundary ->
    TargetVisibleBoundaryOutput profile view

/-- Exact conditional payload appended by the row-5 executor. -/
abbrev Output
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (proof : focus.Active previous) :=
  Generated profile
    (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)

/-- Literal accumulated stage emitted by row 5. -/
abbrev Stage
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :=
  Hypostructure.Core.Residual.Focus.Stage focus (Output profile)

/-- Framework-owned focus inherited by every row-5 successor. -/
abbrev Profile.SuccessorFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :=
  Hypostructure.Core.Residual.Focus.successor focus (Output profile)

/-- Retrieve the exact row-5 output from the accumulated successor ledger. -/
def Profile.outputQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.SuccessorFocus
      fun stage active => Output profile stage.previous active :=
  Hypostructure.Core.Residual.Focus.ActiveQuery.latest

/-- Counted refinement selecting exactly the open target-visible row-5
terminal. Closed positive-gap and zero-quotient siblings remain inactive and
are never converted into row-6 inputs. -/
def Profile.targetVisibleRefinement
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    Hypostructure.Core.Residual.Focus.Refinement profile.SuccessorFocus :=
  profile.outputQuery.tagEqualTo
    (fun _stage _active generated => generated.terminal)
    .targetVisibleBoundary

/-- Framework-owned focus inherited by row 6. It is live exactly when row 5
emitted its target-visible boundary residual. -/
abbrev Profile.TargetVisibleFocus
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :=
  Hypostructure.Core.Residual.Focus.refine profile.SuccessorFocus
    profile.targetVisibleRefinement

/-- Retrieve the exact open row-5 boundary payload under the refined focus.
The generated row-5 output is read from the ledger and never copied. -/
def Profile.targetVisibleBoundaryQuery
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    Hypostructure.Core.Residual.Focus.ActiveQuery profile.TargetVisibleFocus
      fun stage active =>
        TargetVisibleBoundaryOutput profile
          (Hypostructure.Core.Residual.Focus.ActiveView.of
            stage.previous active.parent) :=
  (profile.outputQuery.selectedTag
    (fun _stage _active generated => generated.terminal)
    .targetVisibleBoundary).map fun _stage _active selected =>
      selected.val.targetVisible selected.property

namespace Generated

variable {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
variable {profile : Profile Previous focus Potential Current}
variable {view : ActiveView focus}

/-- Exact payload work is the sum of the generated CT outputs actually
present on this branch.  Missing downstream stages cost zero. -/
def checks (generated : Generated profile view) : Nat :=
  generated.rank.checks +
    (generated.support.map fun support => support.checks).getD 0 +
    (generated.classClosure.map fun closure => closure.checks).getD 0

/-- Recover the gap payload only from its generated terminal. -/
def positiveGapOutput (generated : Generated profile view)
    (isGap : generated.terminal = .positiveStructuralGap) :
    PositiveGapOutput profile view :=
  generated.positiveGap isGap

/-- Recover the zero-boundary payload only from its generated terminal. -/
def zeroBoundaryOutput (generated : Generated profile view)
    (isZero : generated.terminal = .zeroBoundaryQuotient) :
    ZeroBoundaryOutput profile view :=
  generated.zeroBoundary isZero

/-- Recover the target-visible residual only from its generated terminal. -/
def targetVisibleOutput (generated : Generated profile view)
    (isVisible : generated.terminal = .targetVisibleBoundary) :
    TargetVisibleBoundaryOutput profile view :=
  generated.targetVisible isVisible

end Generated

private def positiveGapOfC4
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (output : Hypostructure.CT15.C4Output profile.rankCapability view) :
    PositiveGapOutput profile view := by
  let gap := (profile.fullRankToGap.read view.previous view.proof).fromC4
    view output
  let closedRange :=
    (profile.closedRangeCriterion.read view.previous view.proof).closedRangeOfGap
      gap
  exact {
    gap := gap
    closedRange := closedRange
    directed :=
      StructuralGradient.DirectedExhaustivenessCertificate.ofClosedRange
        closedRange
  }

private def positiveGapOfFullRankLedger
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (output : Hypostructure.CT15.FullRankLedgerOutput
      profile.rankCapability view) : PositiveGapOutput profile view := by
  let gap :=
    (profile.fullRankToGap.read view.previous view.proof).fromFullRankLedger
      view output
  let closedRange :=
    (profile.closedRangeCriterion.read view.previous view.proof).closedRangeOfGap
      gap
  exact {
    gap := gap
    closedRange := closedRange
    directed :=
      StructuralGradient.DirectedExhaustivenessCertificate.ofClosedRange
        closedRange
  }

private def zeroBoundaryOfClosure
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (output : Hypostructure.Core.NormalForm.ClassClosure.ZeroQuotientOutput profile.closureProfile
      profile.closureRegistration view) : ZeroBoundaryOutput profile view :=
  {
    closure := output
    boundaryZero := output.boundaryZero
      (profile.targetComplete.read view.previous view.proof)
  }

private def targetVisibleOfClosure
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (output : Hypostructure.Core.NormalForm.ClassClosure.TargetVisibleOutput profile.closureProfile view) :
    TargetVisibleBoundaryOutput profile view :=
  {
    closure := output
    inWindow := profile.inWindowOfVisible view output.residual.hit.value
      output.residual.targetVisible
    positiveCapacity := profile.positiveCapacityOfVisible view
      output.residual.hit.value output.residual.targetVisible
    nonzeroFlux := profile.nonzeroFluxOfVisible view
      output.residual.hit.value output.residual.targetVisible
  }

private def gapGeneratedOfC4
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (rank : Hypostructure.CT15.Routed profile.rankCapability view)
    (isC4 : rank.terminal = .c4) : Generated profile view :=
  let output := positiveGapOfC4 profile view (rank.c4Output isC4)
  {
    terminal := .positiveStructuralGap
    rank := rank
    support := none
    classClosure := none
    positiveGap := fun _equal => output
    zeroBoundary := fun equal => by cases equal
    targetVisible := fun equal => by cases equal
  }

private def gapGeneratedOfFullRankLedger
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (rank : Hypostructure.CT15.Routed profile.rankCapability view)
    (isFull : rank.terminal = .fullRankLedger) : Generated profile view :=
  let output := positiveGapOfFullRankLedger profile view
    (rank.fullRankLedgerOutput isFull)
  {
    terminal := .positiveStructuralGap
    rank := rank
    support := none
    classClosure := none
    positiveGap := fun _equal => output
    zeroBoundary := fun equal => by cases equal
    targetVisible := fun equal => by cases equal
  }

private def zeroGenerated
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (rank : Hypostructure.CT15.Routed profile.rankCapability view)
    (support : Hypostructure.CT16.Generated profile.supportSpec
      profile.supportCapability view)
    (closure : Hypostructure.Core.NormalForm.ClassClosure.Generated profile.closureProfile
      profile.closureRegistration view)
    (isZero : closure.terminal = .zeroQuotient) : Generated profile view :=
  let output := zeroBoundaryOfClosure profile view
    (closure.zeroQuotientPropagation isZero)
  {
    terminal := .zeroBoundaryQuotient
    rank := rank
    support := some support
    classClosure := some closure
    positiveGap := fun equal => by cases equal
    zeroBoundary := fun _equal => output
    targetVisible := fun equal => by cases equal
  }

private def visibleGenerated
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus)
    (rank : Hypostructure.CT15.Routed profile.rankCapability view)
    (support : Hypostructure.CT16.Generated profile.supportSpec
      profile.supportCapability view)
    (closure : Hypostructure.Core.NormalForm.ClassClosure.Generated profile.closureProfile
      profile.closureRegistration view)
    (isVisible : closure.terminal = .targetVisible) : Generated profile view :=
  let output := targetVisibleOfClosure profile view
    (closure.targetVisibleResidual isVisible)
  {
    terminal := .targetVisibleBoundary
    rank := rank
    support := some support
    classClosure := some closure
    positiveGap := fun equal => by cases equal
    zeroBoundary := fun equal => by cases equal
    targetVisible := fun _equal => output
  }

/-- Counted deterministic CT15 -> CT16 -> ClassClosure generation on one exact
active view.  The actual `Counted` values are composed in execution order, so
no downstream stage discards and reconstructs predecessor work.  ClassClosure
is called exactly once and only after CT15 rank drop and a whole-support CT16
result. -/
def generateActiveCounted
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) : Counted (Generated profile view) :=
  let alignment := profile.codeClosureAlignment.read view.previous view.proof
  (Hypostructure.CT15.generateCounted profile.rankCapability view).bind
    fun rank =>
      match isRank : rank.terminal with
      | .c4 => Counted.pure (gapGeneratedOfC4 profile view rank isRank)
      | .fullRankLedger =>
          Counted.pure (gapGeneratedOfFullRankLedger profile view rank isRank)
      | .rankDrop =>
          let rankDrop := rank.rankDropOutput isRank
          (Hypostructure.CT16.generateCounted profile.supportSpec
            profile.supportCapability view).bind fun support =>
              match isSupport : support.terminal with
              | .properSupport =>
                  False.elim (alignment.properSupportImpossible view rankDrop
                    (support.properSupportResidual isSupport))
              | .exactCode =>
                  let exactCode := support.exactCodeCertificate isSupport
                  (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
                    profile.closureProfile profile.closureRegistration view).map
                    fun closure =>
                      match isClosure : closure.terminal with
                      | .zeroQuotient =>
                          zeroGenerated profile view rank support closure
                            isClosure
                      | .targetVisible =>
                          let visible := closure.targetVisibleResidual isClosure
                          let avoids := alignment.exactCodeAvoids view rankDrop
                            exactCode
                          False.elim
                            (avoids visible.residual.hit.index
                              visible.residual.targetVisible)
              | .mismatch =>
                  let mismatch := support.closedTypeMismatchResidual isSupport
                  (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
                    profile.closureProfile profile.closureRegistration view).map
                    fun closure =>
                      match isClosure : closure.terminal with
                      | .targetVisible =>
                          visibleGenerated profile view rank support closure
                            isClosure
                      | .zeroQuotient =>
                          let zero := closure.zeroQuotientPropagation isClosure
                          let hasVisible := alignment.mismatchVisible view
                            rankDrop mismatch
                          let hit := closure.scan.hitOfHasHit (by
                            rw [closure.scan_eq]
                            exact hasVisible)
                          False.elim (zero.avoids hit.index hit.sound)

/-- Deterministic semantic value generated by the counted row-5 chain. -/
def generateActive
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) : Generated profile view :=
  (generateActiveCounted profile view).value

private theorem rankGeneration_checks_eq_value
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) :
    (Hypostructure.CT15.generateCounted profile.rankCapability view).checks =
      (Hypostructure.CT15.generateCounted
        profile.rankCapability view).value.checks := by
  rw [Hypostructure.CT15.generateCounted_checks]
  rfl

private theorem closureGeneration_checks_eq_value
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) :
    (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
        profile.closureProfile profile.closureRegistration view).checks =
      (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
        profile.closureProfile profile.closureRegistration view).value.checks := by
  rw [Hypostructure.Core.NormalForm.ClassClosure.generateCounted_checks]
  exact (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
    profile.closureProfile profile.closureRegistration
      view).value.checks_eq_canonical_scan.symm

@[simp] theorem generateActiveCounted_checks
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (view : ActiveView focus) :
    (generateActiveCounted profile view).checks =
      (generateActiveCounted profile view).value.checks :=
  by
    let alignment := profile.codeClosureAlignment.read view.previous view.proof
    unfold generateActiveCounted
    simp only [Counted.bind, Counted.map, Counted.pure]
    split
    next isRank =>
      simp [Generated.checks, gapGeneratedOfC4]
    next isRank =>
      simp [Generated.checks, gapGeneratedOfFullRankLedger]
    next isRank =>
      split
      next isSupport =>
        exact (alignment.properSupportImpossible view
          ((Hypostructure.CT15.generateCounted
            profile.rankCapability view).value.rankDropOutput isRank)
          ((Hypostructure.CT16.generateCounted profile.supportSpec
            profile.supportCapability view).value.properSupportResidual
              isSupport)).elim
      next isSupport =>
        split
        next isClosure =>
          rw [rankGeneration_checks_eq_value,
            Hypostructure.CT16.generateCounted_checks_eq_value,
            closureGeneration_checks_eq_value]
          simp only [Generated.checks, zeroGenerated, Option.map_some,
            Option.getD_some]
          omega
        next isClosure =>
          let rankDrop := (Hypostructure.CT15.generateCounted
            profile.rankCapability view).value.rankDropOutput isRank
          let exactCode := (Hypostructure.CT16.generateCounted
            profile.supportSpec profile.supportCapability
              view).value.exactCodeCertificate isSupport
          let visible :=
            (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
              profile.closureProfile profile.closureRegistration
                view).value.targetVisibleResidual isClosure
          exact (alignment.exactCodeAvoids view rankDrop exactCode
            visible.residual.hit.index visible.residual.targetVisible).elim
      next isSupport =>
        split
        next isClosure =>
          rw [rankGeneration_checks_eq_value,
            Hypostructure.CT16.generateCounted_checks_eq_value,
            closureGeneration_checks_eq_value]
          simp only [Generated.checks, visibleGenerated, Option.map_some,
            Option.getD_some]
          omega
        next isClosure =>
          let rankDrop := (Hypostructure.CT15.generateCounted
            profile.rankCapability view).value.rankDropOutput isRank
          let mismatch := (Hypostructure.CT16.generateCounted
            profile.supportSpec profile.supportCapability
              view).value.closedTypeMismatchResidual isSupport
          let closure :=
            (Hypostructure.Core.NormalForm.ClassClosure.generateCounted
              profile.closureProfile profile.closureRegistration view).value
          let zero := closure.zeroQuotientPropagation isClosure
          let hasVisible := alignment.mismatchVisible view rankDrop mismatch
          let hit := closure.scan.hitOfHasHit (by
            rw [closure.scan_eq]
            exact hasVisible)
          exact (zero.avoids hit.index hit.sound).elim

/-- Complete polynomial envelope used only to prove boundedness.  The exact
count remains branch-sensitive and is defined by `Generated.checks`. -/
def completeEnvelope
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    PolynomialCheckBudget (ActiveView focus) :=
  (profile.rankCapability.polynomialBudget.add
    profile.supportCapability.completeWorkBudget).add
      (Hypostructure.Core.NormalForm.ClassClosure.generationBudget profile.closureProfile)

theorem Generated.checks_le_completeEnvelope
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    {profile : Profile Previous focus Potential Current}
    {view : ActiveView focus} (generated : Generated profile view) :
    generated.checks <= (completeEnvelope profile).checks view := by
  have rankBound : generated.rank.checks <=
      profile.rankCapability.polynomialBudget.checks view :=
    generated.rank.checks_le_limit
  have supportBound :
      (generated.support.map fun support => support.checks).getD 0 <=
        profile.supportCapability.completeWorkBudget.checks view := by
    cases generated.support with
    | none => simp
    | some support =>
        simpa [Hypostructure.CT16.Capability.worstCaseChecks] using
          support.checks_le_worstCase
  have closureBound :
      (generated.classClosure.map fun closure => closure.checks).getD 0 <=
        (Hypostructure.Core.NormalForm.ClassClosure.generationBudget profile.closureProfile).checks view := by
    cases generated.classClosure with
    | none => simp
    | some closure =>
        simpa [Hypostructure.Core.NormalForm.ClassClosure.generationBudget] using
          closure.checks_eq_canonical_scan.le
  exact Nat.add_le_add (Nat.add_le_add rankBound supportBound) closureBound

/-- Exact active payload schedule with a polynomial envelope derived entirely
from the three framework executors. -/
def activeGenerationBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    PolynomialCheckBudget (ActiveView focus) :=
  let envelope := completeEnvelope profile
  {
    size := envelope.size
    checks := fun view => (generateActiveCounted profile view).checks
    coefficient := envelope.coefficient
    degree := envelope.degree
    bounded := by
      intro view
      rw [generateActiveCounted_checks]
      exact (generateActiveCounted profile view).value.checks_le_completeEnvelope
        |>.trans (envelope.bounded view)
  }

/-- Reindex the active payload budget to the literal predecessor.  Inactive
predecessors have no payload work; active predecessors use the exact Core
proof selected by the focus. -/
def payloadBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current) :
    PolynomialCheckBudget Previous :=
  let activeBudget := activeGenerationBudget profile
  {
    size := fun previous =>
      match (focus.select previous).value with
      | .isTrue proof => activeBudget.size (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | .isFalse _absent => 0
    checks := fun previous =>
      match (focus.select previous).value with
      | .isTrue proof =>
          activeBudget.checks (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | .isFalse _absent => 0
    coefficient := activeBudget.coefficient
    degree := activeBudget.degree
    bounded := by
      intro previous
      cases selected : (focus.select previous).value with
      | isTrue proof => exact activeBudget.bounded (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)
      | isFalse absent => simp
  }

private theorem generateActiveCounted_checks_eq_payloadBudget
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (proof : focus.Active previous) :
    (generateActiveCounted profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks =
      (payloadBudget profile).checks previous := by
  unfold payloadBudget
  cases selected : (focus.select previous).value with
  | isTrue selectedProof =>
      have equal : selectedProof = proof := Subsingleton.elim _ _
      cases equal
      simp [selected, activeGenerationBudget]
  | isFalse absent => exact (absent proof).elim

/-- The sole row-5 ledger extension.  Core runs the focus selector once,
executes the counted chain only on the active branch, and appends one sealed
output to the literal predecessor. -/
def run
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) :
    Counted (Stage profile) :=
  Hypostructure.Core.Residual.Focus.runCountedPayload
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    focus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact => by
      change (generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks = _
      exact generateActiveCounted_checks_eq_payloadBudget profile previous proof)

@[simp] theorem run_previous
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) :
    (run profile previous).value.previous = previous := by
  unfold run
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_previous
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    focus (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact => by
      change (generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks = _
      exact generateActiveCounted_checks_eq_payloadBudget profile previous proof)

/-- The successor focus remains active after an active row-5 execution.  This
proof is framework-owned so downstream code never reconstructs the focused
ledger constructor. -/
def runActiveProof
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    profile.SuccessorFocus.Active (run profile previous).value := by
  change focus.Active (run profile previous).value.previous
  rw [run_previous]
  exact active

/-- Reading row 5's latest payload after an active run returns the exact value
generated by that run.  No selector, CT execution, or payload is repeated. -/
theorem outputQuery_run_of_active
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    profile.outputQuery.read (run profile previous).value
        (runActiveProof profile previous active) =
      generateActive profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous active) := by
  unfold runActiveProof run generateActive
  cases selected : (focus.select previous).value with
  | isTrue proof =>
      have equal : proof = active := Subsingleton.elim _ _
      cases equal
      simp only [Hypostructure.Core.Residual.Focus.runCountedPayload]
      rw [selected]
      rfl
  | isFalse absent => exact (absent active).elim

/-- Exact active work is focus selection plus the generated branch payload. -/
theorem run_checks_of_active
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (active : focus.Active previous) :
    (run profile previous).checks =
      focus.selectionBudget.checks previous +
        (payloadBudget profile).checks previous := by
  simpa [run, PolynomialCheckBudget.add] using
    Hypostructure.Core.Residual.Focus.runCountedPayload_checks_of_active
      (Output := fun previous proof => Generated profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
      focus (payloadBudget profile)
      previous
      (fun proof _selectionChecks _selectionExact =>
        generateActiveCounted profile (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
      (fun proof _selectionChecks _selectionExact => by
        change (generateActiveCounted profile
          (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks = _
        exact generateActiveCounted_checks_eq_payloadBudget profile previous proof)
      active

/-- Inactive siblings pay only the exact focus-selection work. -/
theorem run_checks_of_inactive
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) (inactive : Not (focus.Active previous)) :
    (run profile previous).checks = focus.selectionBudget.checks previous := by
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_checks_of_inactive
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    focus
    (payloadBudget profile) previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact => by
      change (generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks = _
      exact generateActiveCounted_checks_eq_payloadBudget profile previous proof)
    inactive

/-- Every row-5 run satisfies the composed focus-plus-payload polynomial
envelope. -/
theorem run_checks_bounded
    {focus : Hypostructure.Core.Residual.Focus.Profile Previous}
    (profile : Profile Previous focus Potential Current)
    (previous : Previous) :
    (run profile previous).checks <=
      (focus.selectionBudget.add (payloadBudget profile)).coefficient *
        ((focus.selectionBudget.add (payloadBudget profile)).size previous + 1) ^
          (focus.selectionBudget.add (payloadBudget profile)).degree := by
  exact Hypostructure.Core.Residual.Focus.runCountedPayload_checks_bounded
    (Output := fun previous proof => Generated profile
      (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    focus (payloadBudget profile)
    previous
    (fun proof _selectionChecks _selectionExact =>
      generateActiveCounted profile (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof))
    (fun proof _selectionChecks _selectionExact => by
      change (generateActiveCounted profile
        (Hypostructure.Core.Residual.Focus.ActiveView.of previous proof)).checks = _
      exact generateActiveCounted_checks_eq_payloadBudget profile previous proof)

end Hypostructure.PDE.FastTrack.DirectedExhaustiveness

#print axioms Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run
#print axioms Hypostructure.PDE.FastTrack.DirectedExhaustiveness.outputQuery_run_of_active
#print axioms Hypostructure.PDE.FastTrack.DirectedExhaustiveness.run_checks_bounded
