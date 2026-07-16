# Node [144] repair: split classification from semantic closure

## Defect freeze

- Defect ID: `EG64-node144-classifier-vs-closure`.
- Stable node: `[144]`.
- Failed implication: for every exact homogeneous same-token matching or star
  above the fixed routing-label threshold, the two selected germs already
  construct either a named sparse-exit certificate or a complete decorated
  Type-B entry.
- Smallest verified ancestors: the exact classwise overload and homogeneous
  pattern outputs at `[140]`, `[142]`, and `[143]`.
- Exact negated residual: an exact overloaded token-role fibre and homogeneous
  pattern whose deterministic finite coarse scan returns two distinct equal
  coarse-code pairs together with their selected-window attachment maps and
  their two proof-carrying canonical BFS germs, but without a sparse-exit or
  Type-B consumer certificate.
- Classification: level-2 contract split followed by a level-3 semantic
  consumer repair. The source manuscript remains unchanged during this
  sketch.

The old box combines two different proof moves: a finite classification that
is already locally executable, and the still-open semantic discharge of the
collision. The repair preserves the theorem by separating them. Node `[144]`
becomes the exact classifier; a new downstream semantic-consumer node owns the
old sparse-exit/Type-B conclusion.

## Directed branch state

The active state is

`B144 = (ctx, activation, routed overload, homogeneous pattern, token-role
fibre, exact pattern list, absent quadratic-cap branch)`.

Every field is constructed from `[140]`, `[142]`, or `[143]`; no near-cubic
estimate, cold-window data, Boolean realization, or Type-B entry is imported.
The exact local list is `SurplusPatternCoarseRouting.patternPairs`. It is
duplicate-free and has length 49. The exact code universe has 48 values.

The sole outgoing state is `collisionResidual`: an actual result of
   `Core.FiniteCodeCollision.decide`, retaining the run equality, two distinct
   source pairs, code equality, literal structural attachment maps, and the
   two canonical BFS germs.

The output has one unique consumer, the new semantic bottleneck block.
That consumer must refine delayed attachment mismatch, parallel germs, cubic
separator, compatible open-open high separator, and endpoint failure. It may
not treat any of these records as a sparse exit or Type-B entry without the
corresponding certificate.

## Quantifier normalization

The classifier is parameterized by the exact overload and homogeneous audit
already returned by node `[140]`, `[142]`, or `[143]`; it never reruns the
node-`[137]` decision.  It proves only

```
exists collision,
  decide coarseCodes coarseCode patternPairs = .collision collision
  and first != second
  and coarseCode first = coarseCode second
  and exact attachment maps and canonical germs are retained.
```

It does not prove equality of the attachment maps, equality of external
response, existence of a separating context, existence of a smaller
representative, or a Type-B assignment. The pendant-leaf tree counterexample
therefore attacks only the old semantic implication and not this finite
classification.

## Both-sides test

| Branch | Payment or progress | Exact consumer |
|---|---|---|
| Coarse collision | Strict finite refinement: actual ordered collision, exact maps and BFS germs | new semantic bottleneck consumer block |

The no-overload branch is owned exclusively by node `[138]`; it is not an
outgoing branch of node `[144]`.  The collision is computed from the frozen
predecessor state, and no downstream conclusion is accepted as input.

## CT and ownership worksheet

- The overload/capacity decision remains owned by the existing classwise CT9
  profile.
- The 48-code collision is a local deterministic finite-code scan owned by
  `Core.FiniteCodeCollision` and the graph-specific code/map layer in
  `Graph.SurplusPatternCoarseRouting`.
- The Erdős module is a thin instantiation at sizes `49,49,49`.
- The collision branch is an intended typed handoff, not C1--C5.
- The semantic consumer is not smuggled into a `Consumer` function field.

The reference runner scans only the literal 49-element pattern. Its collision
work is at most `49^2` code comparisons. Constructing the two selected germs
uses the existing ordered BFS work bound on the current graph. No graph,
subgraph, coloring, context, path-family, selected-window family, or support
universe is enumerated.

## Leaf-totality for the repaired node

| Leaf | Exact output | Status |
|---|---|---|
| overload | computed collision residual with exact run provenance | typed handoff to the unique semantic bottleneck consumer |

This table is intentionally local to node `[144]`. The former semantic
closure theorem and every global consequence that used it move to the new
consumer node and remain unverified until that consumer is discharged. This
does not weaken the main theorem or assert the old conclusion; it corrects the
dependency graph so that the real open residual is visible.

## TeX--Lean repair after red-team PASS

After a PASS verdict only:

1. rename diagram node `[144]` to “fixed coarse bottleneck classification”;
2. add one downstream white node for “semantic sparse-exit / Type-B
   bottleneck consumers” and redirect the old global consequences through it;
3. replace the node-`[144]` detailed row and correspondence row by the exact
   classifier statement above;
4. keep the original same-token bottleneck lemma and geometric-closure theorem
   explicitly open at the new consumer;
5. integrate the compiled classifier, transfer fixture, work theorem, web
   declaration groups, and implementation log; and
6. require zero yellow nodes and exact declaration coverage.

## Autonomous derivation ledger

| Required statement | Resolution |
|---|---|
| collision is computed rather than proof-selected | execute `FiniteCodeCollision.decide`; eliminate `.unique` by the 48-versus-49 bound; retain the exact result equality |
| selected pairs are distinct | use nodup of the exact homogeneous pattern and `OrderedCollision.first_ne_second_of_nodup` |
| attachment maps and germs belong to those exact pairs | retain the existing `StructuralAttachmentMaps` and `CanonicalCollisionGerms` indexed by the computed collision |
| collision branch has a consumer without proof injection | register the semantic consumer as a downstream proof node taking the residual itself, not a function from residual to desired conclusions |
| old global statements do not silently use the classifier | move their dependency to the new consumer node and leave them unimplemented |

No missing semantic lemma is carried as an assumption. The semantic gap is
preserved as the explicit downstream residual.
