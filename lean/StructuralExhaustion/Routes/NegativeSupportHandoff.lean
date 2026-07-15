import StructuralExhaustion.Graph.NegativeSupportHandoff

namespace StructuralExhaustion.Routes.NegativeSupportHandoff

open StructuralExhaustion

universe u

variable {V : Type u}

abbrev Source (object : Graph.FiniteObject V) :=
  Graph.NegativeSupportHandoff.ConnectedNegativeSupport object

/-- Ordinary high-surplus continuation.  The witness is indexed by the exact
negative support, so its center cannot come from a different local residual. -/
structure OrdinaryResidual {object : Graph.FiniteObject V}
    (source : Source object) where
  highSurplus : source.HighSurplusWitness

/-- The high-surplus branch is a pure typed handoff. -/
def ordinary {object : Graph.FiniteObject V} (source : Source object)
    (highSurplus : source.HighSurplusWitness) :
    OrdinaryResidual source :=
  ⟨highSurplus⟩

@[simp]
theorem ordinary_highSurplus {object : Graph.FiniteObject V}
    (source : Source object)
    (highSurplus : source.HighSurplusWitness) :
    (ordinary source highSurplus).highSurplus = highSurplus :=
  rfl

/-- Producer output of a decorated exit.  The application-specific semantic
predicates are carried unchanged to the consumer. -/
structure ExitHandoff
    (object : Graph.FiniteObject V)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  source : Source object
  decorated : Graph.NegativeSupportHandoff.DecoratedHandoff object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source

/-- Type-preserving decorated consumer residual. -/
structure DecoratedResidual
    (object : Graph.FiniteObject V)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  source : Source object
  decorated : Graph.NegativeSupportHandoff.DecoratedHandoff object
    ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe source

/-- Route an exact decorated exit output into the local surplus ledger without
rebuilding its graph, core, paths, or semantic evidence. -/
def decorated
    {object : Graph.FiniteObject V}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe) :
    DecoratedResidual object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe where
  source := handoff.source
  decorated := handoff.decorated

@[simp]
theorem decorated_source
    {object : Graph.FiniteObject V}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe) :
    (decorated handoff).source = handoff.source :=
  rfl

@[simp]
theorem decorated_data
    {object : Graph.FiniteObject V}
    {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
    {FanSafe : V → V → V → Prop}
    (handoff : ExitHandoff object ContextSafe ForbiddenFree CoreFree Uncompressible
      FanSafe) :
    (decorated handoff).decorated = handoff.decorated :=
  rfl

/-- Join of the two incoming local branches.  This is deliberately a tagged
sum: ordinary high-surplus data and decorated exit data have different
contracts, and no predicate from one constructor is available in the other. -/
inductive Entry
    (object : Graph.FiniteObject V)
    (ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop)
    (FanSafe : V → V → V → Prop) where
  | ordinary (source : Source object) (residual : OrdinaryResidual source)
  | decorated (residual : DecoratedResidual object ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe)

namespace Entry

variable
  {object : Graph.FiniteObject V}
  {ContextSafe ForbiddenFree CoreFree Uncompressible : Finset V → Prop}
  {FanSafe : V → V → V → Prop}

/-- The exact source residual survives the branch join. -/
def source :
    Entry object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe → Source object
  | .ordinary source _ => source
  | .decorated residual => residual.source

/-- The counted vertex support survives the branch join definitionally. -/
def core
    (entry : Entry object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    Finset V :=
  entry.source.core

/-- Both constructors retain the same local negative-charge fact, but no
constructor-specific semantic predicate is promoted across the join. -/
theorem negative
    (entry : Entry object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) :
    (Graph.NegativeSupportHandoff.chargeProfile object entry.core).netQuarterCharge < 0 := by
  cases entry with
  | ordinary source residual => exact source.negative
  | decorated residual => exact residual.source.negative

@[simp]
theorem source_ordinary (source : Source object) (residual : OrdinaryResidual source) :
    Entry.source (.ordinary source residual :
      Entry object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) = source :=
  rfl

@[simp]
theorem source_decorated
    (residual : DecoratedResidual object ContextSafe ForbiddenFree CoreFree
      Uncompressible FanSafe) :
    Entry.source (.decorated residual :
      Entry object ContextSafe ForbiddenFree CoreFree Uncompressible FanSafe) =
        residual.source :=
  rfl

end Entry

end StructuralExhaustion.Routes.NegativeSupportHandoff
