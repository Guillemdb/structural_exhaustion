import Erdos64EG.OfficialStatement
import Erdos64EG.CT1
import Erdos64EG.CT2
import Erdos64EG.CT3
import Erdos64EG.CT1InducedP13
import Erdos64EG.CT12InducedP13Packing
import Erdos64EG.CT10P13LabelAlgebra

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
-/
