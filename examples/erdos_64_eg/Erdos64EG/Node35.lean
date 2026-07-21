import Erdos64EG.Node34

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [35]: finite rank-reducing dependence

The support-stratified node-[31] rank profile and node [32]'s literal strict edge
determine a CT15 pair circuit without enumerating quotients, supports, or
contexts.  The circuit contains the selected final-carrier proposal, its
distinct identified coordinates, and the functional singleton determination.
The paper also retains, at this same cross-panel branch point, the selected
inclusion-minimal support certificate that node [36] audits at the original
atom interface.

The node-[31] CT15 candidate is proof-carrying: every collision already owns
its support-stratified determination certificate.  Node [35] merely selects
that certificate from the rank circuit.  It receives no application input;
Core retrieves node [33] from the accumulated residual and preserves every
sibling branch.
-/

noncomputable abbrev Node35PairCircuit {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual) :=
  (p13CurvatureRankProfile (Node21Context node18)).PairCircuit

noncomputable abbrev Node35DeterminationSupportProfile {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) :=
  p13CurvatureDeterminationSupportProfile (Node21Context node18)

noncomputable abbrev Node35DeterminationCertificate {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) :=
  (Node35DeterminationSupportProfile node18).Certificate

/-- The support certificate selected for the exact support-stratified-rank collision.
The equalities are the all-and-only bridge needed by the subsequent original-
interface audit: the certificate is for this circuit's code, coordinates, and
final carrier. -/
structure Node35CollisionSupportCertificate {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (circuit : Node35PairCircuit node18) : Type (u + 3) where
  certificate : Node35DeterminationCertificate node18
  quotientCodeExact : certificate.quotientCode =
    circuit.candidate.quotientCode
  basisCoordinateExact : certificate.basisCoordinate =
    circuit.basisCoordinate
  determinedExact : certificate.determined = circuit.determined
  carrierExact : certificate.carrier = circuit.candidate.carrier

/-- Node [32] already returns CT15's literal declared-coordinate rank loss. -/
theorem node35RankDropOnDeclaredCoordinates {V : Type u}
    {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    (_node31 : Node31Output node18 bounded node21 low)
    (rankDrop : Node32RankDrop node18) :
    (p13CurvatureRankProfile (Node21Context node18)).targetRank <
      (p13CurvatureCoordinates (Node21Context node18)).card := by
  simpa [Node32RankDrop, p13CurvatureCoordinates] using rankDrop

/-- CT15's proof-level pair-circuit extractor on the literal node-[32] edge. -/
noncomputable def node35PairCircuit {V : Type u}
    {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    {bounded : Node19Low residual node18}
    {node21 : Node21Output node18 bounded}
    {low : Node22Low residual node18 bounded node21}
    (node31 : Node31Output node18 bounded node21 low)
    (rankDrop : Node32RankDrop node18) :
    Node35PairCircuit node18 :=
  (p13CurvatureRankProfile (Node21Context node18))
    |>.pairCircuitOfRankDrop
      (node35RankDropOnDeclaredCoordinates node18 node31 rankDrop)

/-- Extract the exact support certificate already owned by CT15's selected
rank candidate.  This is a graph/CT15 projection, not application routing. -/
noncomputable def node35CollisionSupportCertificate {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (circuit : Node35PairCircuit node18) :
    Node35CollisionSupportCertificate node18 circuit := by
  let rankProfile := p13CurvatureRankProfile (Node21Context node18)
  let certificate := CT15.SupportStratifiedRank.Profile.certificate
    rankProfile circuit
  exact {
    certificate := certificate
    quotientCodeExact := circuit.candidate.certify_code _ _ _ _
    basisCoordinateExact := circuit.candidate.certify_basis _ _ _ _
    determinedExact := circuit.candidate.certify_determined _ _ _ _
    carrierExact := circuit.candidate.certify_carrier _ _ _ _
  }

/-- Node [35]'s one dependence datum. -/
structure Node35Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (low : Node22Low residual node18 bounded node21)
    (node31 : Node31Output node18 bounded node21 low)
    (rankDrop : Node32RankDrop node18) : Type (u + 3) where
  circuit : Node35PairCircuit node18
  circuitExact : circuit = node35PairCircuit node18 node31 rankDrop
  supportCertificate : Node35CollisionSupportCertificate node18 circuit

namespace Node35Output

/-- The exact framework determination certificate consumed by node [36]. -/
abbrev certificate (output : Node35Output node18 bounded node21 low node31 rankDrop) :
    Node35DeterminationCertificate node18 :=
  output.supportCertificate.certificate

end Node35Output

/-- The node-[35] active yes cursor.  Node [34]'s full-rank constructor and
the earlier node-[20] bypass are transported literally by Core. -/
abbrev Node35Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data rankDrop => Node35Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current rankDrop)
    residual

/-- Framework-owned `[33] → [35]` mapper.  Erdős code supplies only the
CT15 circuit extraction local to this paper node. -/
noncomputable def node35P13RankCircuit {V : Type u}
    {facts} [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node33Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node35Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuation
    (Output := fun _ data rankDrop => Node33Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current rankDrop)
    fun residual data rankDrop node33 => by
        cases node33
        let node18 := data.previous
        let bounded := data.outerProof
        let node21 := data.outerOutput
        let low := data.innerProof
        let node31 := data.current
        let circuit := node35PairCircuit node18 node31 rankDrop
        exact {
          circuit := circuit
          circuitExact := rfl
          supportCertificate :=
            node35CollisionSupportCertificate node18 circuit
        }

noncomputable def runInitialThroughNode35 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode33 residual).mapYesStage
    node35P13RankCircuit

/-- Pair-circuit extraction is proof-level; node [35] scans no finite or
ambient universe. -/
def node35LocalChecks : Nat := 0

theorem node35LocalChecks_eq_zero : node35LocalChecks = 0 := rfl

#print axioms node35RankDropOnDeclaredCoordinates
#print axioms node35PairCircuit
#print axioms node35CollisionSupportCertificate
#print axioms node35P13RankCircuit
#print axioms runInitialThroughNode35

end Erdos64EG.Internal
