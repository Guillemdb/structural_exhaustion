import Erdos64EG.OfficialStatement
import Erdos64EG.CT1
import Erdos64EG.CT2
import Erdos64EG.CT3
import Erdos64EG.CT1InducedP13
import Erdos64EG.CT12InducedP13Packing
import Erdos64EG.CT10P13LabelAlgebra
import Erdos64EG.CT6SparseSurplus
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
import Erdos64EG.CT14TypeBChoiceLedger
import Erdos64EG.CT14TypeBAssignedCharge
import Erdos64EG.CT14TypeARemainingDischarge
import Erdos64EG.CT14TypeBBoundaryTransfer
import Erdos64EG.CT14TypeBSupportSize
import Erdos64EG.CT14TypeBBoundaryDeficit
import Erdos64EG.CT14TypeBUnconditionalDeficit
import Erdos64EG.CT14TypeBPostLedger
import Erdos64EG.CT12SparseEnvelope
import Erdos64EG.CT15BaselineSpineDemand

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
two-degenerate profile, and executes node `[129]` through the reusable CT15
baseline-demand profile. The canonical empty coordinate family makes the
definition unconditional with exact deficit equal to the cubic bit budget;
no linear deficit estimate is asserted.
-/
