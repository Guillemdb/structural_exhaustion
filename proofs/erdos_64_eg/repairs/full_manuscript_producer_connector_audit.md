# Full manuscript producer and connector audit

Date: 2026-07-16

This audit distinguishes three graphs that must not be conflated:

1. the numbered manuscript decision diagram;
2. the Lean theorem-dependency workflow exported by `Erdos64EG.WebExport`;
3. the producer/consumer obligations at the current white frontier.

## Verified root reachability

The regenerated `proof-slice` workflow has 96 stages and 96 typed links. All
96 stages are reachable from `proof-slice.official`, which is the exported
node-1 theorem root. The three previously orphaned components are connected by
the following exact compositions:

- `p13-multiscale-curvature` to `p13-node21-partxi-route`: the route is indexed
  by the identical `VerifiedP13MultiScaleCurvaturePrefix` and maps only the
  graph-owned selected-window list;
- `type-b-residual-center-ledger` to `type-b-local-fan-mass`: the CT14 endpoint
  stores the identical `VerifiedTypeBResidualCenterLedgerPrefix` and scans only
  its selected local centers;
- `homogeneous-pattern` to `coarse-bottleneck-classification`: the classifier
  stores the identical `VerifiedHomogeneousPatternPrefix` and scans the actual
  49-pair pattern against the fixed 48-state local code.

The frontend test `keeps every exported proof-slice stage reachable from node
1` recomputes this transitive closure from the generated artifact.

## Diagram versus theorem dependency

All 194 displayed nodes are topologically reachable from node 1 when the
declared cross-part continuations are included. A visual edge is not
automatically a Lean dependency edge: some mathematical branch tests use a
generic theorem proved earlier in the workflow. In particular, adding direct
workflow edges for displayed arrows `[35] -> [36]` or `[68] -> [69]` would
create cycles, because the reusable replacement/high-center results are
already predecessors of the branch-specific stages. These arrows require an
explicit execution adapter if the exported workflow is ever required to
mirror decision order; they must not be represented by cyclic provenance.

Green nodes `[25]` and `[67]` also have earlier unconditional Lean producers
(`p13-packing` and `ct2`/`high-center-structure`) even though the diagram draws
them after currently white branch nodes. Their present green status records
the proved objects, not closure of those white incoming branches.

## Open producer cut

The first white producer cut is `[22]`, `[48]`, `[76]`, `[85]`, `[145]`,
`[160]`, and `[176]`.

- `[22]`, `[48]`, and `[160]` share the quarantined simultaneous-realization
  obligation. Node `[21]` proves coordinate counts, not realization of every
  91-bit assignment. No Boolean cube or caller-supplied assignment may replace
  the missing graph theorem.
- The rigorous non-Boolean bypass needs the graph-owned node-`[24]`
  `P13WindowDensityStructuralTheorem`, including coverage, the density cap, and
  the strict window-only quarter budget.
- `[176]` needs a graph-owned global ordinary/grouped Type B entry schedule,
  occurrence family, within-role incidence theorem, and CT14 mass bridge. Node
  `[84]` is only local and cannot manufacture this family.
- `[76]` and `[85]` are join closures. They remain downstream of the actual
  near-cubic spine estimate and the global Type B fan-mass producer; neither
  can be implemented by restating the manuscript inequality as an input.
- `[145]` is downstream of the non-Boolean node-`[24]` density/spine producer.

Two first producer units are now compiled without closing these obligations.
The selected-window prefix-family runner supplies the exact all-window
first-obstruction/all-complete traversal and `91 * p13` work envelope, but its
pointwise graph machine and realization/gluing semantics remain open. The
fixed-skeleton entry schedule supplies one computed surplus-or-cubic-stub entry
per selected window, exact coverage and cubic counts, but still requires fixed
D4--D7 reconstruction, F2--F4 routing, and bounded-multiplicity aggregation
before it can yield the node-`[24]` density theorem.

## Locality and trust requirements

Every new producer must construct its schedule from the retained node-1
context, expose exact predecessor provenance, and pass a typed payload to each
consumer. Computation may traverse declared local schedules, selected windows,
observed clauses, or fixed alphabets. It may not enumerate ambient graphs,
contexts, supports, response universes, or Boolean assignments. All production
theorems remain subject to the repository's sole-HSS trust audit.
