import Erdos64EG.P13Nodes25To34Refinement
import Erdos64EG.P13Node36To37
import Erdos64EG.P13Node38To39
import StructuralExhaustion.Core.ZeroWorkBudget

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Framework-routed nodes [35]--[47]

This module consumes the stable node-[24] residual and the exact branch value
already produced by `p13Nodes25To34Run`.  It performs only the two proof-level
audits in the original Part-III diagram: original-interface context validity
and final-carrier location.  The graph framework owns support inclusion,
proper/whole classification, CT3 compression, closed reduction, and exact
quotient injectivity.
-/

abbrev P13Node35Output
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) :=
  VerifiedP13Node35BranchD
    residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
      residual.node28 residual.node29 residual.node30 residual.node31
      residual.node32 branch.rankDrop

noncomputable def P13Node33Stage.node35
    {residual : P13Node24RefinementResidual.{u}}
    (branch : P13Node33Stage residual) : P13Node35Output residual branch :=
  branch.output.node35

/-- The framework-owned accumulated payload on the existing `[33] → [35]`
edge.  It retains the literal node-[33] branch and constructs node `[35]`
from that value, without restating either object in an Erdős-specific ledger. -/
abbrev P13Node35Stage (residual : P13Node24RefinementResidual.{u}) :=
  Core.ResidualRefinement.State.DependentSuccessor
    P13Node33Stage
    (fun residual branch => P13Node35Output residual branch)
    residual

/-- Refine the rank-drop edge by retrieving its exact node-[33] payload from
the accumulated ledger.  This is zero-copy handoff plumbing; the mathematical
node-[35] output remains exactly `P13Node33Stage.node35`. -/
noncomputable def p13Node35Refinement {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available P13Node33Stage) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) P13Node35Stage :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual branch => branch.node35)

/-- Continue only the original rank-drop edge of the node-[32] decision.
The full-rank edge remains the literal node-[34] branch. -/
noncomputable def p13Nodes25To35Run
    (residual : P13Node24RefinementResidual.{u}) :=
  (p13Nodes25To34Run residual).mapYesStage p13Node35Refinement

theorem p13Nodes25To35Run_exact
    (residual : P13Node24RefinementResidual.{u}) :
    match p13Nodes25To35Run residual with
    | .yesBranch branch =>
        Nonempty (P13Node35Stage branch.state.residual) ∧
          branch.state.residual = residual
    | .noBranch branch =>
        Nonempty (P13Node34Stage branch.state.residual) ∧
          branch.state.residual = residual := by
  unfold p13Nodes25To35Run
  cases p13Nodes25To34Run residual with
  | yesBranch branch =>
      exact ⟨(branch.runStage p13Node35Refinement).state.latest,
        (branch.runStage p13Node35Refinement).residualExact.trans
          (p13Node32State_retains_residual residual)⟩
  | noBranch branch =>
      exact ⟨branch.state.latest,
        branch.residualExact.trans (p13Node32State_retains_residual residual)⟩

abbrev P13Node36Output
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) :=
  VerifiedP13Node36ContextValidity
    residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
      residual.node28 residual.node29 residual.node30 residual.node31
      residual.node32 branch.rankDrop branch.node35

noncomputable def P13Node33Stage.node36
    {residual : P13Node24RefinementResidual.{u}}
    (branch : P13Node33Stage residual) : P13Node36Output residual branch :=
  branch.node35.node36

/-- Node `[40]` is reached only from the universal original-context edge and
the strict-enlargement constructor of node `[38]`. -/
structure VerifiedP13Node40EnlargedSupport
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual)
    (node36 : P13Node36Output residual branch)
    (node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36) : Type (u + 3)
    extends Core.ExactHandoff node38 where
  strict :
    (p13CurvatureDeterminationSupportProfile residual.ctx).SupportLt
      branch.node35.certificate.original branch.node35.certificate.carrier
  locationEdge : previous.location = .enlarged strict
  originalLeCarrier :
    (p13CurvatureDeterminationSupportProfile residual.ctx).supportLe
      branch.node35.certificate.original branch.node35.certificate.carrier
  carrierConnected :
    (p13CurvatureDeterminationSupportProfile residual.ctx).connected
      branch.node35.certificate.carrier
  carrierCarriesBasis :
    (p13CurvatureDeterminationSupportProfile residual.ctx).carries
      branch.node35.certificate.carrier branch.node35.certificate.basisCoordinate
  carrierCarriesDetermined :
    (p13CurvatureDeterminationSupportProfile residual.ctx).carries
      branch.node35.certificate.carrier branch.node35.certificate.determined
  carrierDetermines :
    (p13CurvatureDeterminationSupportProfile residual.ctx).determines
      branch.node35.certificate.carrier branch.node35.certificate.basisCoordinate
        branch.node35.certificate.determined
  minimalSupport : ∀ support,
    (p13CurvatureDeterminationSupportProfile residual.ctx).connected support →
    (p13CurvatureDeterminationSupportProfile residual.ctx).determines support
      branch.node35.certificate.basisCoordinate branch.node35.certificate.determined →
    (p13CurvatureDeterminationSupportProfile residual.ctx).supportLe support
      branch.node35.certificate.carrier →
    (p13CurvatureDeterminationSupportProfile residual.ctx).supportLe
      branch.node35.certificate.carrier support

/-- The exact surviving outcomes of nodes `[36]`--`[40]`.  The at-atom
universal branch is absent because node `[39]` closes it by CT3. -/
inductive P13Node36To40Route
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) where
  | targetDefect
      (node37 : P13Node37TargetDefect branch.node36)
  | enlarged
      (node36 : P13Node36Output residual branch)
      (node38 : VerifiedP13Node38ProperRepresentativeDecision
        residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
          residual.node28 residual.node29 residual.node30 residual.node31
          residual.node32 branch.rankDrop branch.node35 node36)
      (node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38)

/-- Execute the original context and support-location diamonds. -/
noncomputable def routeP13Node36To40
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) :
    P13Node36To40Route residual branch := by
  let node36 := branch.node36
  cases contextEdge : node36.decision with
  | defective context mismatch =>
      exact .targetDefect (node36.node37 context mismatch contextEdge)
  | universal allContexts =>
      let node38 := node36.node38 allContexts contextEdge
      cases locationEdge : node38.location with
      | atOriginal equal =>
          exact False.elim (node38.node39 equal locationEdge)
      | enlarged strict =>
          exact .enlarged node36 node38 {
            previous := node38
            previousExact := rfl
            strict := strict
            locationEdge := locationEdge
            originalLeCarrier := strict.1
            carrierConnected := branch.node35.certificate.carrier_connected
            carrierCarriesBasis :=
              branch.node35.certificate.carrier_carries_basis
            carrierCarriesDetermined :=
              branch.node35.certificate.carrier_carries_determined
            carrierDetermines := branch.node35.certificate.carrier_determines
            minimalSupport := branch.node35.certificate.minimal
          }

theorem routeP13Node36To40_exhaustive
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) :
    (∃ node37, routeP13Node36To40 residual branch = .targetDefect node37) ∨
      (∃ node36 node38 node40,
        routeP13Node36To40 residual branch = .enlarged node36 node38 node40) := by
  cases routed : routeP13Node36To40 residual branch with
  | targetDefect node37 => exact Or.inl ⟨node37, rfl⟩
  | enlarged node36 node38 node40 =>
      exact Or.inr ⟨node36, node38, node40, rfl⟩

/-- Node `[41]` reads the graph-owned proper/whole tag of the exact enlarged
carrier. -/
abbrev VerifiedP13Node41CarrierScope
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual)
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    (node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38) :=
  Core.ExactPropertyHandoff node40 (fun _ =>
    branch.node35.certificate.carrier.OriginalEligible ∨
      branch.node35.certificate.carrier.IsWhole)

def VerifiedP13Node40EnlargedSupport.node41
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    (node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38) :
    VerifiedP13Node41CarrierScope residual branch node40 :=
  Core.ExactPropertyHandoff.refl node40
    branch.node35.certificate.carrier.scope_exhaustive

/-- Node `[42]`: a proper final carrier already stores the literal CT3
compression certified by quotient admission. -/
theorem VerifiedP13Node41CarrierScope.node42
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    (_node41 : VerifiedP13Node41CarrierScope residual branch node40)
    (proper : branch.node35.certificate.carrier.OriginalEligible) : False :=
  Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
    proper branch.node35.certificate.representative

/-- Node `[43]` is the paper-named view of the framework's generic exact
property handoff for the whole-carrier edge. -/
abbrev VerifiedP13Node43WholeDelocalization
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual)
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    (node41 : VerifiedP13Node41CarrierScope residual branch node40) :=
  Core.ExactPropertyHandoff node41 (fun _ =>
    branch.node35.certificate.carrier.IsWhole)

def VerifiedP13Node41CarrierScope.node43
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    (node41 : VerifiedP13Node41CarrierScope residual branch node40)
    (whole : branch.node35.certificate.carrier.IsWhole) :
    VerifiedP13Node43WholeDelocalization residual branch node41 :=
  Core.ExactPropertyHandoff.refl node41 whole

/-- Node `[44]` adds only the reusable one--three repair identity. -/
structure VerifiedP13Node44RepairIdentity
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual)
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    {node41 : VerifiedP13Node41CarrierScope residual branch node40}
    (node43 : VerifiedP13Node43WholeDelocalization residual branch node41) :
    Type (u + 3) extends Core.ExactHandoff node43 where
  repairIdentity : ∀ internalVertices boundaryLeaves internalEdges
      cycleRank surplus : Int,
    3 * internalVertices + surplus + boundaryLeaves =
        2 * (internalEdges + boundaryLeaves) →
    cycleRank = internalEdges - internalVertices + 1 →
    internalVertices = boundaryLeaves - 2 + 2 * cycleRank - surplus
  graphRepairIdentity : ∀ (component : Graph.OneThreeRepair.Component residual.ctx.G.Vertex),
    (component.internal.card : Int) =
      component.boundary.card - 2 + 2 * component.cycleRank - component.surplus

def VerifiedP13Node43WholeDelocalization.node44
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    {node41 : VerifiedP13Node41CarrierScope residual branch node40}
    (node43 : VerifiedP13Node43WholeDelocalization residual branch node41) :
    VerifiedP13Node44RepairIdentity residual branch node43 where
  previous := node43
  previousExact := rfl
  repairIdentity := oneThreeRepair_identity
  graphRepairIdentity := oneThreeRepair_component_identity

/-- Node `[45]`: a candidate whose single final carrier is the whole graph is
injective on all raw labels. -/
structure VerifiedP13Node45ClosedExactBarrier
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual)
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    {node41 : VerifiedP13Node41CarrierScope residual branch node40}
    {node43 : VerifiedP13Node43WholeDelocalization residual branch node41}
    (node44 : VerifiedP13Node44RepairIdentity residual branch node43) : Type (u + 3)
    extends Core.ExactHandoff node44 where
  exactRawLabels : Function.Injective
    branch.output.circuit.candidate.quotientCode

noncomputable def VerifiedP13Node44RepairIdentity.node45
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    {node41 : VerifiedP13Node41CarrierScope residual branch node40}
    {node43 : VerifiedP13Node43WholeDelocalization residual branch node41}
    (node44 : VerifiedP13Node44RepairIdentity residual branch node43) :
    VerifiedP13Node45ClosedExactBarrier residual branch node44 where
  previous := node44
  previousExact := rfl
  exactRawLabels := by
    exact
      Graph.SupportStratifiedDetermination.Candidate.code_injective_of_equal_carrier_whole
        (coordinateSupport := p13CurvatureSupport)
        branch.output.circuit.candidate branch.node35.carrierExact
          node43.certificate

/-- Node `[46]`: injectivity contradicts the retained distinct-coordinate
collision selected at node `[35]`. -/
theorem VerifiedP13Node45ClosedExactBarrier.node46
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    {node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38}
    {node41 : VerifiedP13Node41CarrierScope residual branch node40}
    {node43 : VerifiedP13Node43WholeDelocalization residual branch node41}
    {node44 : VerifiedP13Node44RepairIdentity residual branch node43}
    (node45 : VerifiedP13Node45ClosedExactBarrier residual branch node44) : False :=
  branch.output.properDependence
    (node45.exactRawLabels branch.output.quotientIdentifies)

/-- Close every enlarged-support route at its existing proper/whole edges. -/
theorem P13Node36To40Route.enlarged_impossible
    {residual : P13Node24RefinementResidual.{u}}
    {branch : P13Node33Stage residual}
    {node36 : P13Node36Output residual branch}
    {node38 : VerifiedP13Node38ProperRepresentativeDecision
      residual.ctx residual.node21 residual.node24 residual.node26 residual.node27
        residual.node28 residual.node29 residual.node30 residual.node31
        residual.node32 branch.rankDrop branch.node35 node36}
    (node40 : VerifiedP13Node40EnlargedSupport residual branch node36 node38) : False := by
  let node41 := node40.node41
  rcases node41.certificate with proper | whole
  · exact node41.node42 proper
  · let node43 := node41.node43 whole
    let node44 := node43.node44
    let node45 := node44.node45
    exact node45.node46

/-- The completed Part-III rank-drop route leaves only its displayed
target-defect terminal; every context-universal branch closes at node `[39]`,
`[42]`, or `[46]`. -/
theorem routeP13Node36To40_rankDrop_closed
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node33Stage residual) :
    ∃ node37 : P13Node37TargetDefect branch.node36,
      routeP13Node36To40 residual branch = .targetDefect node37 := by
  cases routed : routeP13Node36To40 residual branch with
  | targetDefect node37 => exact ⟨node37, rfl⟩
  | enlarged node36 node38 node40 =>
      exact False.elim (P13Node36To40Route.enlarged_impossible node40)

/-- Node `[47]` is the exact cross-panel continuation of node `[34]`'s
full-rank edge.  It does not consume a rank-drop terminal. -/
structure VerifiedP13Node47FullRankResidual
    (residual : P13Node24RefinementResidual.{u})
    (branch : P13Node34Stage residual) : Type (u + 3)
    extends Core.ExactHandoff branch.output where
  fullRank : p13CurvatureTargetRank residual.ctx =
    (p13RemainderCurvatureProfile residual.ctx).wedgeCount
  maximalFamily :
    ∃ family : Finset (P13CurvatureCoordinate residual.ctx),
      (p13CurvatureFunctionalRankProfile residual.ctx).Survives family ∧
      family.card = (p13RemainderCurvatureProfile residual.ctx).wedgeCount

def P13Node34Stage.node47
    {residual : P13Node24RefinementResidual.{u}}
    (branch : P13Node34Stage residual) :
    VerifiedP13Node47FullRankResidual residual branch where
  previous := branch.output
  previousExact := rfl
  fullRank := branch.output.fullRankExact
  maximalFamily := branch.output.maximalFamily

#print axioms p13Nodes25To35Run_exact

end Erdos64EG.Internal
