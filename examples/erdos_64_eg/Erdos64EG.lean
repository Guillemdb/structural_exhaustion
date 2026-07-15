import Erdos64EG.OfficialStatement
import Erdos64EG.CT1
import Erdos64EG.CT2
import Erdos64EG.CT3
import Erdos64EG.CT1InducedP13
import Erdos64EG.CT12InducedP13Packing
import Erdos64EG.P13RemainderResidual
import Erdos64EG.CT10P13LabelAlgebra
import Erdos64EG.SurplusScaleSplit
import Erdos64EG.CT14P13PositiveDeficiency
import Erdos64EG.CT15RemainderCurvature
import Erdos64EG.CT6SparseSurplus
import Erdos64EG.TypeBEntryRouting
import Erdos64EG.CT9SurplusPairs
import Erdos64EG.CT1HighCenterStructure
import Erdos64EG.CT10SurplusPortClassification
import Erdos64EG.CT9OpenPortPairs
import Erdos64EG.CT7OpenPortResponses
import Erdos64EG.CT5PortShoulderLedger
import Erdos64EG.CT7OpenPortCompatibility
import Erdos64EG.CT10HighCenterPortDichotomy
import Erdos64EG.CT5TriangularShoulderCompletion
import Erdos64EG.CT2BridgeContraction
import Erdos64EG.CT1TriangularPortReturn
import Erdos64EG.CT10TriangularFirstLanding
import Erdos64EG.CT9TriangularCrossShoulder
import Erdos64EG.CT5FanClosedPort
import Erdos64EG.CT14FanClosedPortMass
import Erdos64EG.CT14HybridFanIncidence
import Erdos64EG.CT1FanWindowCycle
import Erdos64EG.CT1TwoWindowCycle
import Erdos64EG.CT9FanLabelPacking
import Erdos64EG.CT9MarkedFanLabelPacking
import Erdos64EG.CT14CertificateClosedFanCharge
import Erdos64EG.CT14PositiveDeficitFanEntry
import Erdos64EG.CT14LocalB1Entry
import Erdos64EG.CT14PositiveDeficitCandidate
import Erdos64EG.CT14CertificateClosedCandidate
import Erdos64EG.CT12TypeBDemandSystem
import Erdos64EG.CT12TypeBCompletion
import Erdos64EG.CT12TypeBOverlapSupport
import Erdos64EG.CT12TypeBResolution
import Erdos64EG.CT14DegreeFourTypeBLedger
import Erdos64EG.CT14TypeBChoiceLedger
import Erdos64EG.CT14TypeBAssignedCharge
import Erdos64EG.CT14TypeARemainingDischarge
import Erdos64EG.CT14TypeBBoundaryTransfer
import Erdos64EG.CT14TypeBSupportSize
import Erdos64EG.CT14TypeBBoundaryDeficit
import Erdos64EG.CT14TypeBUnconditionalDeficit
import Erdos64EG.CT14TypeBPostLedger
import Erdos64EG.CT12DegreeFourB2Routing
import Erdos64EG.CT14TypeBResidualCenterLedger
import Erdos64EG.CT12SparseEnvelope
import Erdos64EG.SparsePressureEnvelopeRoute
import Erdos64EG.CT6SurplusPortActivation
import Erdos64EG.CT15BaselineSpineDemand
import Erdos64EG.CT15SparsePairResponses
import Erdos64EG.CT9AllPairAnchorLedger
import Erdos64EG.CT9CapacityTokenLedger
import Erdos64EG.CT9CoupledClassOverload
import Erdos64EG.CT9HomogeneousPattern

/-!
Structural-exhaustion implementation of the current Erdős Problem 64 proof
slice.

The verified prefix contains the official-statement boundary, the exact
Mersenne return algebra, proof-carrying positive and avoiding CT1 executions,
lexicographic vertex/edge minimal selection, the certificate-driven CT2
no-proper-core theorem, the registered local CT1-to-CT2 route, deletion
criticality, high-degree independence, and the CT3 stage spanning boundaried
degree fibres, context universality, replacement, and hereditary
uncompressibility. All theorem-independent cycle, subgraph, replacement,
route, and prefix machinery is imported from the framework graph, CT, and
route layers.  The CT1 block at diagram nodes `[15]`--`[16]` has an avoiding
residual that is literal induced-`P₁₃`-freeness; the sole trusted HSS
external theorem closes that branch against target avoidance, and CT1 retains
the forced induced-path embedding through its exact C1 execution.  The
following CT12 block selects a maximum induced-`P₁₃` packing, proves its
maximal saturation, audits exactly its linear-size peeling schedule,
constructs the exact induced remainder, and verifies both hereditary
`P₁₃`-freeness and absence of every finite internal subgraph of minimum degree
at least three.
The next CT10 block classifies all nonempty attachment labels to a fixed
induced `P₁₃`, proves the exact 399-row table and size distribution,
defines the manuscript relations `C_s` and `Ω₂`, and retains that verified
classification on the identical CT12-selected graph.
The following CT6 block scans the selected graph's declared vertex order,
rules out the first non-cubic neighbour of a high centre using deletion
criticality, and produces the exact degree-surplus ledger with a linear outer
scan and a quadratic primitive neighbour-test bound.
The next CT9 block consumes that exact CT6 residual through the registered
framework route and returns either the small-surplus certificate or two
distinct surplus slots, using only the explicit slot list.
Further framework-native blocks expose the local selected-port data:
CT1 certifies four-cycle avoidance and its high-neighbourhood consequences;
CT10 classifies canonical selected ports as open or triangular; CT9 groups
open ports by centre; the registered overload-only CT9-to-CT7 route compares
their endpoint adjacency responses; and CT5 certifies the exact two-shoulder
ledger. CT7 then proves the exact same-centre compatibility alternative, CT10
classifies all incident high-centre ports, and CT5 proves the four
triangular-shoulder completion clauses. CT2 proves bridgelessness by literal
contraction, and its framework-owned return transition feeds a one-check CT1
stage producing the exact triangular-port return path, cycle arithmetic, and
initial landing split. CT10 then classifies every actual completion incidence
as central, cross-triangular, or outside and composes that audit with the exact
CT1 return. CT9 refines two triangular-port shoulder pairs to the exact
high-shoulder or capacity-one cross-edge survivor. CT5 then instantiates the
actual packed-window/remainder partition and proves that any assigned
fan-compatible open pair contributes two fan-closed ports and four distinct
incidence carriers by an exact four-site ledger. The downstream global Type B
routing then begins with a framework-owned CT5-to-CT14 transition: CT14 scans
the actual cubic-closed-neighbour subtype, proves its multiplicity is at least
two, and derives the positive quarter-deficit numerator. A registered
CT14-to-CT14 refinement then scans exactly two actual non-centre incidences
per cubic-closed neighbour, proves their endpoints disjoint from four-cycle
avoidance, partitions the exact window/non-window multiplicities, and proves
that their half-credits pay the local deficit with three quarter-units of
slack under the marked-fan bound `degree center ≤ 8`. A graph-owned CT1 stage
then constructs the internal-gap, centre-crossing, and interlacing
same-window cycles as literal Mathlib walks and derives direct-cycle-freeness
from the selected avoiding branch with zero enumeration. A second graph-owned
CT1 stage joins two vertex-disjoint induced windows with orientation-independent
bridges and proves the exact `4+|i-j|+|a-b|` cycle exclusion. The positive-
deficit fan analysis then begins with a graph-owned CT9 representative-packing
profile: for every certificate-marked fan, the legal pairwise-compatible label
map on the actual incident ports yields the exact bound `degree center ≤ 8`
through eight fixed capacity-one fibres. A second graph-owned CT9 refinement
uses two distinct positions in a marked non-singleton label to block two slots,
giving the exact stronger bound `degree center ≤ 7`. The fixed position
certificates are compiled separately, and no attachment-code or label-family
universe is enumerated. A graph-owned CT14 stage then scans the actual marked
fan ports, counts cubic-closed members, and derives nonnegative
closed-neighbourhood charge from the defining certificate-closed inequality.
Finally, the application supplies one actual marked fan and two assigned,
compatible fan-closed ports. The existing graph-owned mass and hybrid-incidence
profiles consume the previously proved marked-fan cap and derive the literal
closed count, positive quarter-deficit, endpoint-disjoint credit ledger, and
paying inequality. A framework-owned semantic projection identifies that
verified CT14 object with the exact local B1 ledger. The next framework-owned
layer defines the corresponding positive-deficit Type B candidate as a proved
finite subset of those literal incidences: every window incidence is
mandatory, reserve-used incidences are forbidden, and selected non-window
incidences must pay the exact remaining demand. Its finite-fibre proof does
not evaluate a powerset, and the all-incidence candidate is constructed from
the verified B1 inequality whenever the ordinary reserve is locally free.
The certificate-closed branch is represented by the analogous framework
profile on the actual neighbour ports: the exact weight is computed from the
assigned internal degree, with cubic-closed weight `-1` and every open weight
at least `3`; the selected weight offsets the exact center charge. Deletion
criticality proves each selected endpoint is cubic and hence
outside the high-center set; the verified certificate charge constructs the
complete-neighbour candidate when the reserve is locally free. Concrete
cross-centre completion and the remaining center, window, replacement, and
delocalization reflection clauses remain outside this prefix.

The current endpoint additionally retains the choice-free Type B post-ledger
bound, proves the node `[126]` sparse envelope through the reusable CT12
two-degenerate profile, executes node `[129]` through the reusable CT15
baseline-demand profile, and consumes the exact activated residual in the
free/blocked pair-response CT15 block at nodes `[130]`--`[132]`.  The pair
stage proves its exact partition, retains local blocker and shortest-connector
certificates, and proves admitted quotient injectivity by the generic
certified-reduction/minimality theorem.  Its schedule is at most quartic and
no graph, path, connected-subgraph, quotient, or context universe is
materialized.  The current CT9 route then accounts for every scheduled pair
in one exact first-port/product-role partition.  Its five roles are the four
admitted structural blocker kinds and the literal `freeAnchor` residual.  Blocked
pairs retain their complete first-hit certificate for the canonical blocker
ledger; every free-anchor fibre member is proved blocker-free and carries its
first selected surplus port as the primitive-carrier token.  The route uses
the existing quartic pair schedule and a fixed five-role scan.  Nodes
`[133]`--`[136]` then refine that unchanged pair collection to the exact
window/remainder/primitive capacity-token universe, prove the selected
`P₁₃` window-join identity, and partition every pair among 25 total roles.
The following classwise CT9 decision covers nodes `[137]`--`[139]` and
`[141]`: positive coupled excess returns an actual overloaded token--role
fibre and its unique token-class route, while the other side proves
`σ² ≤ (450 bmax + 1)n`.  Both audits are cubic, with the explicit common
bound `225 n³`, and materialize no graph family, matching family, Boolean
cube, or recursive search tree.
The next graph-owned CT9 consumer covers nodes `[140]`, `[142]`, and `[143]`:
it projects the actual overloaded fibre and runs a deterministic greedy
maximal-matching scan.  The sharp `(L-1)(2L-3)` bound produces a matching or
star of the class threshold without enumerating either pattern family.
At the other green boundaries, a core squared-scale decision implements node
`[19]`, the graph charge profile implements node `[28]` on the exact packed
remainder, and the degree-four Type B chain implements nodes `[80]`--`[83]`
with certificate provenance fixed before CT12 completion.  Its unresolved,
remaining-negative, and minimal-overlap outputs remain explicit residuals;
node `[75]` proves that every ordinary residual center is paid by an actual
  assigned surplus unit.  The remainder-curvature CT15 block then implements
  nodes `[29]`--`[35]` from the exact node-`[28]` residual, including the
  surplus-adjusted stub inequality, literal wedge count, and full-rank
  admissible-quotient audit.  The framework-owned proper-delocalization route
  closes nodes `[40]`--`[42]` by an actual boundary-fixing support embedding
  and the existing CT3 context audit.  The compiled descriptor therefore has
  exactly seventy green Chapter 1 nodes.
-/
