import Erdos64EG.P13PartIWindowDensityTriage
import Erdos64EG.TypeANode63Support

namespace Erdos64EG.Internal.TypeANodes57To63Provenance

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Existing node `[57]`: retain the exact node-[56] strict-quarter handoff. -/
structure VerifiedNode57Residual
    (node24 : VerifiedP13WindowDensityOutput ctx node21) where
  previous : P13QuarterNetDeficiencyHandoff ctx node21 node24.coverage
  exactPrevious : previous = p13ClosureRobustPartIV node24

noncomputable def node57
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    VerifiedNode57Residual node24 where
  previous := p13ClosureRobustPartIV node24
  exactPrevious := rfl

/-- Existing node `[58]`: the exact quarter-unit net-charge numerator on the
same remainder, with no replacement support or alternate decomposition. -/
structure VerifiedNode58Residual
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    (node57 : VerifiedNode57Residual node24) where
  previous : VerifiedNode57Residual node24
  exactPrevious : previous = node57
  netQuarter : Int
  netQuarterExact : netQuarter =
    4 * (p13NetDeficiencyNumerator ctx : Int) -
      ((p13RemainderVertices ctx).card : Int)

noncomputable def node58
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    (node57 : VerifiedNode57Residual node24) : VerifiedNode58Residual node57 where
  previous := node57
  exactPrevious := rfl
  netQuarter := 4 * (p13NetDeficiencyNumerator ctx : Int) -
    ((p13RemainderVertices ctx).card : Int)
  netQuarterExact := rfl

/-- On the exact large-budget net-cap branch, the yes exit of node `[59]` is
impossible and the original no edge carries strict negative net charge. -/
structure VerifiedNode59NegativeResidual
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    (node58 : VerifiedNode58Residual node57) where
  previous : VerifiedNode58Residual node57
  exactPrevious : previous = node58
  negative : node58.netQuarter < 0

noncomputable def node59
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    (node58 : VerifiedNode58Residual node57) :
    VerifiedNode59NegativeResidual node58 where
  previous := node58
  exactPrevious := rfl
  negative := by
    rw [node58.netQuarterExact]
    have strict := node57.previous.strictQuarter
    have strictInt : (4 * p13NetDeficiencyNumerator ctx : Int) <
        ((p13RemainderVertices ctx).card : Int) := by
      exact_mod_cast strict
    omega

/-- Original node `[60]`: the nonnegative exit of node `[59]` contradicts
the strict negative net charge retained on the identical remainder. -/
theorem node60_impossible
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    (node59 : VerifiedNode59NegativeResidual node58)
    (nonnegative : 0 ≤ node58.netQuarter) : False :=
  (Int.not_lt_of_ge nonnegative) node59.negative

/-- Canonical node-[56] ledger retaining the exact node-[21], coverage, and
strict-quarter predecessor carried by the verified node-[24] output. -/
noncomputable def canonicalLedger
    (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    P13NegativeSupportLocalization.CanonicalQuarterLedger ctx where
  node21 := node21
  coverage := node24.coverage
  pressure := p13ClosureRobustPartIV node24

/-- Exact original node `[61]` CT11 localization, now retaining nodes
`[57]`--`[59]` rather than jumping directly from the quarter predicate. -/
structure VerifiedNode61Residual
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    (node59 : VerifiedNode59NegativeResidual node58) where
  previous : VerifiedNode59NegativeResidual node58
  exactPrevious : previous = node59
  localized : TypeBEntryRouting.VerifiedNode61Residual ctx
  localizedExact : localized =
    P13NegativeSupportLocalization.canonicalNode61 ctx (canonicalLedger node24)

noncomputable def node61
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    (node59 : VerifiedNode59NegativeResidual node58) :
    VerifiedNode61Residual node59 where
  previous := node59
  exactPrevious := rfl
  localized := P13NegativeSupportLocalization.canonicalNode61 ctx
    (canonicalLedger node24)
  localizedExact := rfl

/-- Exact original node `[62]` decision and its existing `[63]`/`[64]`
routes, executed on node `[61]`'s identical localized support. -/
noncomputable def node62
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    {node59 : VerifiedNode59NegativeResidual node58}
    (node61 : VerifiedNode61Residual node59) :
    TypeANode63Support.VerifiedNode62Routed node61.localized :=
  TypeANode63Support.routeNode62 node61.localized

/-- Nodes `[57]`--`[62]` perform one canonical component scan followed by one
degree scan of the selected support. -/
noncomputable def localChecks
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    {node59 : VerifiedNode59NegativeResidual node58}
    (node61 : VerifiedNode61Residual node59) : Nat :=
  (P13NegativeSupportLocalization.Canonical.cells ctx).values.length +
    node61.localized.support.core.card

theorem localChecks_linear
    {node24 : VerifiedP13WindowDensityOutput ctx node21}
    {node57 : VerifiedNode57Residual node24}
    {node58 : VerifiedNode58Residual node57}
    {node59 : VerifiedNode59NegativeResidual node58}
    (node61 : VerifiedNode61Residual node59) :
    localChecks node61 ≤ 2 * ctx.G.object.input.vertices.card := by
  have cells := P13NegativeSupportLocalization.Canonical.scan_linear ctx
  have support : node61.localized.support.core.card ≤
      ctx.G.object.input.vertices.card := by
    rw [← ctx.G.object.card_vertexFinset]
    exact Finset.card_le_card fun vertex _ => ctx.G.object.mem_vertexFinset vertex
  unfold localChecks
  omega

end Erdos64EG.Internal.TypeANodes57To63Provenance
