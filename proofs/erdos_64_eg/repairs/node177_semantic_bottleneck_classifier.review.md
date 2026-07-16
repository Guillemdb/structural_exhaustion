# Independent review: node [177] finite semantic-bottleneck classifier

## Baseline

- Reviewed implementation:
  `Core.FinitePredicateAlignment`,
  `CT10.ExhaustiveClassification.Profile.exactSelection`,
  `Graph.SurplusPatternSemanticBottleneck`, the independent transfer fixture,
  and `Erdos64EG.Internal.semanticBottleneckClassification`.
- Immediate predecessor: the exact node-[144]
  `coarseBottleneckClassification` result on the supplied overload and
  homogeneous audit from nodes [140], [142], and [143].
- Source manuscript hash during the completed review:
  `8017cf48732847533b3ee7873f05eadfb16e5e866d7647582cca7d1995717f5c`.
- Methodology consulted: S-Def, S-Dich, S-Pers, S-Det, S-Rout, S-Trig,
  S-Comp, leaf totality, the both-sides test, and the repair protocol.
- Final verdict: **PASS for the local finite classifier**.  TeX/web integration
  must split the current node-[177] global semantic claim: this green node may
  claim only the finite five-way classifier, while sparse exit, CT3, Type B,
  and fixed-cap closure remain a new white downstream consumer.

## Provenance matrix

| Used fact | Producer | Earlier and exact on this path? | Independent of node [177]? | Verdict |
|---|---|---:|---:|---|
| actual overload | node-[137] CT9 result | yes | yes | pass |
| homogeneous 49-pair audit | nodes [140]/[142]/[143] | yes | yes | pass |
| executable 49-to-48 collision | node [144] `verifiedCollision` | yes, with `decisionExact` | yes | pass |
| literal first/second attachment maps | node [144] collision | yes | yes | pass |
| two canonical BFS germs and exact path comparison | node [144] germ residual | yes | yes | pass |
| semantic trigger | node [144] `semanticTrigger` | yes; the Erdős predecessor is `coarseBottleneckClassification` itself | yes | pass |

`canonicalGeometricPredecessor` is definitionally the canonical node-[144]
runner.  The node-[177] result stores `residualExact`, `source_exact`, and the
verified CT10 stage on this same collision and trigger.  It does not rebuild a
look-alike collision, attachment map, germ, or branch context.

## Quantifier attack

| Claim | Literal domain | Countermodel/weakening attempted | Result |
|---|---|---|---|
| attachment alignment | every selected `WindowIndex`, every `Fin 13` position, both collided-pair slots, all three `PortRole`s | omit a window, endpoint slot, or role | impossible: the product `FinEnum` is exact and `aligned_exact` reconstructs the identical four quantifiers |
| mismatch | first coordinate where the two executable adjacency predicates are not equivalent | replace first hit by an existential mismatch | rejected: `FirstHit` itself is retained, including the clean prefix |
| aligned germ shape | the stored four-constructor `TreePathComparison` | collapse both prefix orientations or assert a geometric consequence | orientations remain distinct; all four constructors retain only their exact computed shape |
| CT10 class | the actual computed residual tag | accept all tags, or accept a caller-selected tag | rejected and repaired: `exactSelection residualTagEnum classify.tag` accepts exactly the computed tag |

There is no injection-to-surjection step, simultaneous-realization claim,
Boolean-cube claim, quotient representative, context-generator claim, or
proof-selected semantic witness.

## Branch and CT audit

The classifier has exactly five exhaustive typed leaves:

| Leaf | Exact evidence retained | Status |
|---|---|---|
| attachment mismatch | actual first hit, mismatch proof, and clean preceding prefix | typed residual |
| aligned left prefix | full attachment alignment and exact left-prefix tag | typed residual |
| aligned right prefix | full attachment alignment and exact right-prefix tag | typed residual |
| aligned root divergence | full attachment alignment and exact root-divergence tag | typed residual |
| aligned after-edge divergence | full attachment alignment and exact after-edge tag | typed residual |

S-Def is the explicit coordinate product and executable adjacency maps.
S-Dich is `classify_total`, obtained by the alignment decision followed by
the four-constructor germ comparison.  S-Pers is the exact predecessor source
stored in `Residual.source/source_exact` and the Erdős `residualExact` theorem.
The acyclic node-[144]-to-[177] handoff needs no S-Meas or S-Rest.

CT10 is no longer ceremonial.  `Profile.exactSelection` scans the five
declared candidate tags, accepts exactly `classify.tag`, has one accepted
class, and runs to the exhaustive terminal.  `SemanticBottleneckClassification`
retains its `VerifiedStage`, whose fields include the exact terminal, trace,
semantic validity, trace validity, populated class, totality, and polynomial
certificate.  `residualAccepted` couples that run to the retained residual.

No leaf asserts sparse exit, CT3 equivalence/compression, Type-B structure,
fixed-cap closure, or a target cycle.  These are downstream obligations, not
vacuous closures of this classifier.

## Practicality and termination

- Largest enumerated graph-local universe:
  `WindowIndex × Fin 13 × Bool × PortRole`.
- Exact size: `78 * packingNumber`.
- Primitive alignment charge: three checks per coordinate (two retained map
  projections and their comparison), hence `234 * packingNumber`.
- CT10 charge: five acceptance checks, one direct scan, and one one-row class
  scan, hence seven checks.
- Exact combined charge: `234 * packingNumber + 7`.
- Vertex bound: the earlier induced-path packing theorem gives
  `13 * packingNumber ≤ |V|`, hence in particular
  `packingNumber ≤ |V|`; Lean proves the advertised
  `234 * packingNumber + 7 ≤ 234 * |V| + 7`.
- Recursion: only structurally finite `FiniteSearch.first` and CT10 table
  scans; there is no cyclic route.
- Hidden global computation: none.  No ambient vertices, graphs, subgraphs,
  paths, embeddings, attachments outside the selected coordinate product,
  colorings, contexts, or homogeneous-pattern pairs are enumerated.

## Ownership and transfer

- Generic first-disagreement execution belongs to `Core`.
- The reusable exact-selected-class constructor and its cardinality/check
  theorems belong to CT10.
- Attachment coordinates and graph semantics belong to `Graph`.
- The Erdős module is a thin instantiation at order 13 and the canonical
  node-[144] predecessor.
- `Examples.FinitePredicateAlignment` executes both alignment branches and a
  theorem-independent exact-selected CT10 stage, retaining terminal, trace,
  semantic validity, trace validity, totality, and the four-check bound on its
  two-tag alphabet.

## Trust and validation

Searches found no `sorry`, `admit`, new `axiom`, or `unsafe` declaration in
the reviewed cone.  The only `native_decide` is the fixed two-element transfer
fixture check.

Focused builds passed:

```text
lake build StructuralExhaustion.CT10.ExhaustiveClassification
lake build StructuralExhaustion.Graph.SurplusPatternSemanticBottleneck
lake build StructuralExhaustion.Examples.FinitePredicateAlignment
lake build Erdos64EG.CT10SemanticBottleneckClassification
```

Focused `#print axioms` results for alignment totality, five-way totality,
CT10 validity, the local work theorem, and the retained CT10 stage contain
only `propext`, `Classical.choice`, and `Quot.sound`.  The official prefix
existence theorem additionally contains exactly the registered HSS theorem,
with no other external mathematical axiom.

Relevant `git diff --check` passed.

## Defect history and disposition

The first audit failed because CT10 accepted `True` on all five tags and its
run was not retained by the Erdős classification bundle.  That run was
semantically independent of the actual classified residual.  The repair
introduced the reusable exact-selected-class CT10 profile, coupled it to
`classify.tag`, retained the complete verified stage, added residual equality
and acceptance fields, revised the work charge from 35 to 7, and reran the
entire focused audit.

There are no remaining blocking or required-cleanup findings in the local
Lean classifier.  The current stronger manuscript node [177] must not be
marked green without the stated TeX/web split and a new white downstream
semantic-consumer node.

**Final verdict: PASS (local classifier; integration split required).**
