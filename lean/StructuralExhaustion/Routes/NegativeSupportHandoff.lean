import StructuralExhaustion.Graph.NegativeSupportHandoff

namespace StructuralExhaustion.Routes.NegativeSupportHandoff

open StructuralExhaustion

universe u

variable {V : Type u}

abbrev Source (object : Graph.FiniteObject V)
    (parameters : Graph.AssignedSupportCharge.Parameters) (threshold : Nat) :=
  Graph.NegativeSupportHandoff.ConnectedNegativeSupportWith object parameters
    threshold

/-- Ordinary high-surplus continuation at an explicit threshold.  The witness
is indexed by the exact negative support, so its center cannot come from a
different local residual. -/
structure OrdinaryResidualAtLeast {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters) (threshold : Nat)
    (source : Source object parameters threshold) where
  highSurplus : source.HighSurplusWitness

/-- The explicit-threshold high-surplus branch is a pure typed handoff. -/
def ordinaryAtLeast {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters) (threshold : Nat)
    (source : Source object parameters threshold)
    (highSurplus : source.HighSurplusWitness) :
    OrdinaryResidualAtLeast parameters threshold source :=
  ⟨highSurplus⟩

/-- No-high continuation at an explicit threshold.  The empty-high-center
certificate is indexed by the exact negative support selected upstream. -/
structure NoHighResidualAtLeast {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters) (threshold : Nat)
    (source : Source object parameters threshold) where
  retainedCore : Finset V := source.core
  noHigh : source.NoHighSurplus

/-- Fully parameterized no-high support entry.  This is the generic route
payload for a Type-A-like branch: the application chooses the baseline, the
high threshold, the signed budget scale, and the exact deficiency/size
quantities.  The route only stores consequences of the literal source support
and supplied branch proof. -/
structure NoHighTypedResidual {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters)
    (threshold deficiency size : Nat)
    (source : Source object parameters threshold) where
  retainedCore : Finset V := source.core
  threshold_eq : threshold = parameters.baseline + 1
  minimumDegreeBaseline : parameters.baseline ≤ object.minDegree
  noHigh : source.NoHighSurplus
  ambientDegree_eq_baseline :
    ∀ vertex ∈ source.core, object.degree vertex = parameters.baseline
  budget :
    Graph.NegativeSupportHandoff.SignedBudgetEntry deficiency size
      parameters.scale

/-- Construct a fully parameterized no-high support entry. -/
def noHighTyped {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters)
    (threshold deficiency size : Nat)
    (source : Source object parameters threshold)
    (threshold_eq : threshold = parameters.baseline + 1)
    (minimumDegreeBaseline : parameters.baseline ≤ object.minDegree)
    (noHighSurplus : source.NoHighSurplus)
    (negativeBudget :
      (parameters.scale : Int) * (deficiency : Int) - (size : Int) < 0) :
    NoHighTypedResidual parameters threshold deficiency size source where
  threshold_eq := threshold_eq
  minimumDegreeBaseline := minimumDegreeBaseline
  noHigh := noHighSurplus
  ambientDegree_eq_baseline :=
    source.ambientDegree_eq_baseline_of_noHigh threshold_eq
      minimumDegreeBaseline noHighSurplus
  budget :=
    Graph.NegativeSupportHandoff.signedBudgetEntry deficiency size parameters.scale
      negativeBudget

/-- The explicit-threshold no-high branch is a pure typed handoff. -/
def noHighAtLeast {object : Graph.FiniteObject V}
    (parameters : Graph.AssignedSupportCharge.Parameters) (threshold : Nat)
    (source : Source object parameters threshold)
    (noHighSurplus : source.NoHighSurplus) :
    NoHighResidualAtLeast parameters threshold source :=
  { noHigh := noHighSurplus }

/-- Producer output of a decorated exit.  The application-specific semantic
predicates are carried unchanged to the consumer. -/
structure ExitHandoff
    (object : Graph.FiniteObject V)
    (parameters : Graph.AssignedSupportCharge.Parameters)
    (threshold : Nat)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  source : Source object parameters threshold
  decorated : Graph.NegativeSupportHandoff.DecoratedHandoffWith object
    parameters threshold
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source

/-- Type-preserving decorated consumer residual. -/
structure DecoratedResidual
    (object : Graph.FiniteObject V)
    (parameters : Graph.AssignedSupportCharge.Parameters)
    (threshold : Nat)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  source : Source object parameters threshold
  decorated : Graph.NegativeSupportHandoff.DecoratedHandoffWith object
    parameters threshold
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source

/-- Route an exact decorated exit output into the local surplus ledger without
rebuilding its graph, core, paths, or semantic evidence. -/
def decorated
    {object : Graph.FiniteObject V}
    {parameters : Graph.AssignedSupportCharge.Parameters}
    {threshold : Nat}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object parameters threshold ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    DecoratedResidual object parameters threshold ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe where
  source := handoff.source
  decorated := handoff.decorated

@[simp]
theorem decorated_source
    {object : Graph.FiniteObject V}
    {parameters : Graph.AssignedSupportCharge.Parameters}
    {threshold : Nat}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object parameters threshold ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (decorated handoff).source = handoff.source :=
  rfl

@[simp]
theorem decorated_data
    {object : Graph.FiniteObject V}
    {parameters : Graph.AssignedSupportCharge.Parameters}
    {threshold : Nat}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object parameters threshold ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    (decorated handoff).decorated = handoff.decorated :=
  rfl

/-- Join of the two incoming local branches.  This is deliberately a tagged
sum: ordinary high-surplus data and decorated exit data have different
contracts, and no predicate from one constructor is available in the other. -/
inductive Entry
    (parameters : Graph.AssignedSupportCharge.Parameters)
    (threshold : Nat)
    (object : Graph.FiniteObject V)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  | ordinary (source : Source object parameters threshold)
      (residual : OrdinaryResidualAtLeast parameters threshold source)
  | decorated (residual : DecoratedResidual object parameters threshold ContextSafe ForbiddenFree
      CoreFree Uncompressible FanSafe)

namespace Entry

variable
  {parameters : Graph.AssignedSupportCharge.Parameters}
  {threshold : Nat}
  {object : Graph.FiniteObject V}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}

/-- The exact source residual survives the branch join. -/
def source :
    Entry parameters threshold object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe →
      Source object parameters threshold
  | .ordinary source _ => source
  | .decorated residual => residual.source

/-- The counted vertex support survives the branch join definitionally. -/
def core
    (entry : Entry parameters threshold object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe) :
    Finset V :=
  entry.source.core

/-- Both constructors retain the same local negative-charge fact, but no
constructor-specific semantic predicate is promoted across the join. -/
theorem negative
    (entry : Entry parameters threshold object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe) :
    (Graph.NegativeSupportHandoff.chargeProfileWith object parameters threshold
      entry.core).netCharge < 0 := by
  cases entry with
  | ordinary source residual => exact source.negative
  | decorated residual => exact residual.source.negative

@[simp]
theorem source_ordinary (source : Source object parameters threshold)
    (residual : OrdinaryResidualAtLeast parameters threshold source) :
    Entry.source (.ordinary source residual :
      Entry parameters threshold object ContextSafe ForbiddenFree CoreFree Uncompressible
        FanSafe) =
        source :=
  rfl

@[simp]
theorem source_decorated
    (residual : DecoratedResidual object parameters threshold ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    Entry.source (.decorated residual :
      Entry parameters threshold object ContextSafe ForbiddenFree CoreFree Uncompressible
        FanSafe) =
        residual.source :=
  rfl

end Entry

end StructuralExhaustion.Routes.NegativeSupportHandoff
