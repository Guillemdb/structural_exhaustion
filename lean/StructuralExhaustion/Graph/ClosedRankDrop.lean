import StructuralExhaustion.CT15.AdmissibleQuotient

namespace StructuralExhaustion.Graph.ClosedRankDrop

open StructuralExhaustion

universe uAmbient uBranch uCoordinate uBoundary uContext

/-!
# Whole-support closure for an admitted finite quotient

This module consumes one quotient which has already passed the local
`CT15.AdmissibleQuotient.Admissible` contract.  In particular, target-response
preservation and the certified-reduction clause are inputs inherited from the
quotient-admission node; no ambient context family is searched here.

Minimality makes every admitted quotient injective.  Consequently a
whole-support rank-drop payload identifying two distinct declared coordinates
closes immediately, while the surviving local output is the exact-label
barrier.
-/

abbrev ResponseSystem := CT15.AdmissibleQuotient.ResponseSystem
abbrev Proposal := CT15.AdmissibleQuotient.Proposal

/-- The sole surviving result of the whole-support admission barrier. -/
structure ExactBarrier
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (system : ResponseSystem.{uCoordinate, uBoundary, uContext})
    (proposal : Proposal system) : Prop where
  injective : Function.Injective proposal.code

/-- Admission already contains the representative reduction needed to turn
minimality into exact label injectivity. -/
theorem exactBarrier
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {system : ResponseSystem.{uCoordinate, uBoundary, uContext}}
    {proposal : Proposal system}
    (quotient : CT15.AdmissibleQuotient.Admissible ctx system proposal) :
    ExactBarrier ctx system proposal :=
  ⟨quotient.injective⟩

/-- An admitted quotient cannot identify two distinct declared coordinates. -/
theorem no_silent_identification
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {system : ResponseSystem.{uCoordinate, uBoundary, uContext}}
    {proposal : Proposal system}
    (quotient : CT15.AdmissibleQuotient.Admissible ctx system proposal)
    {left right : system.Coordinate} (distinct : left ≠ right)
    (identified : proposal.Identifies left right) : False :=
  distinct (quotient.injective identified)

/-- A proof-carrying rank-drop payload at whole support.  Every field is local
to the fixed finite response system and its single admitted proposal. -/
structure RankDropCertificate
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (system : ResponseSystem.{uCoordinate, uBoundary, uContext}) : Type _ where
  proposal : Proposal system
  quotient : CT15.AdmissibleQuotient.Admissible ctx system proposal
  left : system.Coordinate
  right : system.Coordinate
  distinct : left ≠ right
  identified : proposal.Identifies left right

/-- The whole-support rank-drop residual is empty. -/
theorem rankDrop_impossible
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {system : ResponseSystem.{uCoordinate, uBoundary, uContext}}
    (certificate : RankDropCertificate ctx system) : False :=
  no_silent_identification certificate.quotient certificate.distinct
    certificate.identified

/-- One inherited certificate is inspected; no context, quotient, support, or
graph universe is enumerated. -/
def checks : Nat := 1

theorem checks_eq_one : checks = 1 := rfl

end StructuralExhaustion.Graph.ClosedRankDrop
