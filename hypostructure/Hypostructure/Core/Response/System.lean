import Hypostructure.Core.Assembly.AtomContext

/-!
# Domain-independent response systems

A response system separates semantic responses in arbitrary contexts from the
finite coordinates used by an executor.  Coordinate responses are required to
be exact evaluations at decoded contexts; no graph, PDE, sign, or cardinality
convention is built into this layer.
-/

namespace Hypostructure.Core.Response

open Hypostructure.Core

universe uRepresentative uContext uCoordinate uValue
  uAmbient uBranch uInterface uSite uAtom uAssemblyContext
  uMeasure uIncrement

/-- Two literal representatives compared in one response calculation. -/
structure Representatives (Representative : Type uRepresentative) where
  source : Representative
  replacement : Representative

/-- Exact semantic and coordinate response evaluation.

The domain supplies both evaluations and proves that a coordinate is exactly
the response in its decoded context.  Core subsequently owns vector
construction, finite comparison, and transport to universal statements. -/
structure System (Representative : Type uRepresentative) where
  Context : Type uContext
  Coordinate : Type uCoordinate
  Value : Type uValue
  contextResponse : Representative -> Context -> Value
  decode : Coordinate -> Context
  coordinateResponse : Representative -> Coordinate -> Value
  coordinateExact : forall representative coordinate,
    coordinateResponse representative coordinate =
      contextResponse representative (decode coordinate)

namespace System

variable {Representative : Type uRepresentative}

/-- Register coordinates whose evaluation is definitionally evaluation in the
decoded semantic context. -/
def ofDecodedContexts
    (Context : Type uContext) (Coordinate : Type uCoordinate)
    (Value : Type uValue)
    (contextResponse : Representative -> Context -> Value)
    (decode : Coordinate -> Context) : System Representative where
  Context := Context
  Coordinate := Coordinate
  Value := Value
  contextResponse := contextResponse
  decode := decode
  coordinateResponse := fun representative coordinate =>
    contextResponse representative (decode coordinate)
  coordinateExact := by intros; rfl

/-- Obtain a response system from a registered atom/context assembly.

Representatives are atoms at one exact interface, semantic contexts are the
compatible context type at that interface, and every response is an
observation of the framework-owned assembled ambient object. -/
def ofAssembly
    {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}
    (assembly : AtomContextAssembly.{uAmbient, uBranch, uInterface, uSite,
      uAtom, uAssemblyContext} P E)
    (interface : assembly.Interface)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> assembly.Context interface)
    (Value : Type uValue) (observe : P.Ambient -> Value) :
    System (assembly.Atom interface) :=
  ofDecodedContexts (assembly.Context interface) Coordinate Value
    (fun atom context => observe (assembly.assemble atom context)) decode

@[simp] theorem ofDecodedContexts_coordinateResponse
    (Context : Type uContext) (Coordinate : Type uCoordinate)
    (Value : Type uValue)
    (contextResponse : Representative -> Context -> Value)
    (decode : Coordinate -> Context)
    (representative : Representative) (coordinate : Coordinate) :
    (ofDecodedContexts Context Coordinate Value contextResponse decode).coordinateResponse
        representative coordinate =
      contextResponse representative (decode coordinate) :=
  rfl

end System

/-- A target response represented exactly by a predicate on response values. -/
structure TargetSemantics {Representative : Type uRepresentative}
    (system : System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative) where
  TargetResponse : Representative -> system.Context -> Prop
  Accepts : system.Value -> Prop
  target_iff_accepts : forall representative context,
    TargetResponse representative context <->
      Accepts (system.contextResponse representative context)

namespace TargetSemantics

variable {Representative : Type uRepresentative}
  {system : System.{uRepresentative, uContext, uCoordinate, uValue}
    Representative}

/-- Exact target reflection is inherited by every registered coordinate. -/
theorem coordinate_iff_accepts (semantics : TargetSemantics system)
    (representative : Representative) (coordinate : system.Coordinate) :
    semantics.TargetResponse representative (system.decode coordinate) <->
      semantics.Accepts
        (system.coordinateResponse representative coordinate) := by
  rw [semantics.target_iff_accepts, system.coordinateExact]

/-- Target semantics induced by observing framework-owned assembly. -/
def ofAssembly
    {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}
    (assembly : AtomContextAssembly.{uAmbient, uBranch, uInterface, uSite,
      uAtom, uAssemblyContext} P E)
    (interface : assembly.Interface)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> assembly.Context interface)
    (Target : P.Ambient -> Prop)
    (Value : Type uValue) (observe : P.Ambient -> Value)
    (Accepts : Value -> Prop)
    (reflects : forall (atom : assembly.Atom interface)
      (context : assembly.Context interface),
      Target (assembly.assemble atom context) <->
        Accepts (observe (assembly.assemble atom context))) :
    TargetSemantics
      (System.ofAssembly assembly interface Coordinate decode Value observe) where
  TargetResponse := fun atom context =>
    Target (assembly.assemble atom context)
  Accepts := Accepts
  target_iff_accepts := reflects

/-- An extracted atom/context response represents the target status of its
original ambient object whenever the target is semantically invariant. -/
theorem extractedResponse_iff_target
    {P : Problem.{uAmbient, uBranch}} {E : SemanticEquivalence P}
    (assembly : AtomContextAssembly.{uAmbient, uBranch, uInterface, uSite,
      uAtom, uAssemblyContext} P E)
    {Target : P.Ambient -> Prop} (invariant : TargetInvariant E Target)
    (Value : Type uValue) (observe : P.Ambient -> Value)
    (Accepts : Value -> Prop)
    (reflects : forall {interface : assembly.Interface}
      (atom : assembly.Atom interface) (context : assembly.Context interface),
      Target (assembly.assemble atom context) <->
        Accepts (observe (assembly.assemble atom context)))
    (object : P.Ambient) (site : assembly.Site object) :
    Target object <->
      Accepts (observe (assembly.assemble
        (assembly.atom object site) (assembly.context object site))) := by
  exact (assembly.reconstructedTargetIff invariant object site).symm.trans
    (reflects (assembly.atom object site) (assembly.context object site))

end TargetSemantics

/-- Equality of semantic responses in every context. -/
structure UniversalNeutrality
    {Representative : Type uRepresentative}
    (system : System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative)
    (representatives : Representatives Representative) : Prop where
  equalInContext : forall context,
    system.contextResponse representatives.source context =
      system.contextResponse representatives.replacement context

/-- Target equivalence in every semantic context.  This is deliberately
unoriented: response equality alone contains no progress information. -/
structure TargetCompleteEquivalence
    {Representative : Type uRepresentative}
    {system : System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative}
    (semantics : TargetSemantics system)
    (representatives : Representatives Representative) : Prop where
  targetIff : forall context,
    semantics.TargetResponse representatives.source context <->
      semantics.TargetResponse representatives.replacement context

namespace UniversalNeutrality

variable {Representative : Type uRepresentative}
  {system : System.{uRepresentative, uContext, uCoordinate, uValue}
    Representative}
  {representatives : Representatives Representative}

/-- Universal exact response equality implies target-complete equivalence. -/
def targetComplete (neutral : UniversalNeutrality system representatives)
    (semantics : TargetSemantics system) :
    TargetCompleteEquivalence semantics representatives where
  targetIff := by
    intro context
    have acceptsIff :
        semantics.Accepts
            (system.contextResponse representatives.source context) <->
          semantics.Accepts
            (system.contextResponse representatives.replacement context) := by
      rw [neutral.equalInContext context]
    exact (semantics.target_iff_accepts representatives.source context).trans
      (acceptsIff.trans
        (semantics.target_iff_accepts
          representatives.replacement context).symm)

end UniversalNeutrality

/-- Ordered progress data for representatives.  The strict relation is on an
abstract measure and need not be arithmetic. -/
structure ProgressSystem (Representative : Type uRepresentative) where
  Measure : Type uMeasure
  measure : Representative -> Measure
  Strict : Measure -> Measure -> Prop

/-- Optional signed increment data.  The caller chooses the increment type,
zero, and difference operation and proves the exact increment identity. -/
structure SignedIncrement
    {Representative : Type uRepresentative}
    (progress : ProgressSystem.{uRepresentative, uMeasure} Representative)
    (representatives : Representatives Representative) where
  Increment : Type uIncrement
  zero : Increment
  difference : progress.Measure -> progress.Measure -> Increment
  increment : Increment
  incrementExact : increment = difference
    (progress.measure representatives.source)
    (progress.measure representatives.replacement)

namespace SignedIncrement

variable {Representative : Type uRepresentative}
  {progress : ProgressSystem.{uRepresentative, uMeasure} Representative}
  {representatives : Representatives Representative}

/-- Canonical exact increment registration for a supplied difference law. -/
def ofDifference (Increment : Type uIncrement) (zero : Increment)
    (difference : progress.Measure -> progress.Measure -> Increment) :
    SignedIncrement progress representatives where
  Increment := Increment
  zero := zero
  difference := difference
  increment := difference (progress.measure representatives.source)
    (progress.measure representatives.replacement)
  incrementExact := rfl

end SignedIncrement

/-- The two possible strict orientations of a representative comparison. -/
inductive Direction where
  | sourceToReplacement
  | replacementToSource
deriving DecidableEq, Repr

/-- Strict progress attached to a direction. -/
def StrictAt
    {Representative : Type uRepresentative}
    (progress : ProgressSystem.{uRepresentative, uMeasure} Representative)
    (representatives : Representatives Representative) : Direction -> Prop
  | .sourceToReplacement =>
      progress.Strict (progress.measure representatives.replacement)
        (progress.measure representatives.source)
  | .replacementToSource =>
      progress.Strict (progress.measure representatives.source)
        (progress.measure representatives.replacement)

/-- Registered strict evidence.  It is mathematical input, not a selected
response outcome. -/
structure StrictEvidence
    {Representative : Type uRepresentative}
    (progress : ProgressSystem.{uRepresentative, uMeasure} Representative)
    (representatives : Representatives Representative)
    (direction : Direction) : Prop where
  valid : StrictAt progress representatives direction

/-- Registered evidence that an exact signed increment is nonzero. -/
structure NonzeroEvidence
    {Representative : Type uRepresentative}
    {progress : ProgressSystem.{uRepresentative, uMeasure} Representative}
    {representatives : Representatives Representative}
    (signed : SignedIncrement.{uRepresentative, uMeasure, uIncrement}
      progress representatives) : Prop where
  nonzero : Not (signed.increment = signed.zero)

/-- A domain law converting nonzero signed progress into one of the abstract
strict orientations.  Core, rather than an application node, selects the
resulting direction. -/
structure NonzeroOrientationLaw
    {Representative : Type uRepresentative}
    (progress : ProgressSystem.{uRepresentative, uMeasure} Representative)
    (representatives : Representatives Representative)
    (signed : SignedIncrement.{uRepresentative, uMeasure, uIncrement}
      progress representatives) : Prop where
  strict_of_nonzero : Not (signed.increment = signed.zero) ->
    Exists fun direction => StrictAt progress representatives direction

/-- A target-complete comparison carrying a certified strict orientation.
The constructor is private so the public API can create this value only from
registered strict or nonzero evidence. -/
structure OrientedComparison
    {Representative : Type uRepresentative}
    {system : System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative}
    (semantics : TargetSemantics system)
    (representatives : Representatives Representative)
    (progress : ProgressSystem.{uRepresentative, uMeasure} Representative) where
  private mk ::
  targetComplete : TargetCompleteEquivalence semantics representatives
  direction : Direction
  strict : StrictAt progress representatives direction

namespace OrientedComparison

variable {Representative : Type uRepresentative}
  {system : System.{uRepresentative, uContext, uCoordinate, uValue}
    Representative}
  {semantics : TargetSemantics system}
  {representatives : Representatives Representative}
  {progress : ProgressSystem.{uRepresentative, uMeasure} Representative}

/-- Orient only after target completeness and registered strict evidence. -/
def afterStrict
    (complete : TargetCompleteEquivalence semantics representatives)
    {direction : Direction}
    (evidence : StrictEvidence progress representatives direction) :
    OrientedComparison semantics representatives progress :=
  .mk complete direction evidence.valid

/-- Orient only after target completeness, a registered nonzero law, and an
actual nonzero increment certificate. -/
noncomputable def afterNonzero
    {signed : SignedIncrement.{uRepresentative, uMeasure, uIncrement}
      progress representatives}
    (complete : TargetCompleteEquivalence semantics representatives)
    (law : NonzeroOrientationLaw progress representatives signed)
    (evidence : NonzeroEvidence signed) :
    OrientedComparison semantics representatives progress :=
  let oriented := law.strict_of_nonzero evidence.nonzero
  .mk complete (Classical.choose oriented) (Classical.choose_spec oriented)

/-- Every oriented comparison exposes genuine strict progress. -/
theorem strictExists
    (oriented : OrientedComparison semantics representatives progress) :
    Exists fun direction => StrictAt progress representatives direction :=
  ⟨oriented.direction, oriented.strict⟩

/-- If neither strict orientation is possible, no oriented comparison can be
fabricated from response or target equivalence alone. -/
theorem notNonempty
    (impossible : forall direction,
      Not (StrictAt progress representatives direction)) :
    Not (Nonempty (OrientedComparison semantics representatives progress)) := by
  rintro ⟨oriented⟩
  exact impossible oriented.direction oriented.strict

end OrientedComparison

end Hypostructure.Core.Response
