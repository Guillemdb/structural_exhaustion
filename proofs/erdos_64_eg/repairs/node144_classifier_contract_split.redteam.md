# Red-team re-audit: node [144] classifier/consumer split

## Baseline and verdict

- Audited sketch: `node144_classifier_contract_split.md`.
- Source-manuscript hash before and after this audit:
  `d1b2906e05b57ec419bf2dcd1495064500e13f902e8e9f772ce2dafa66c91363`.
- Focused framework and Erdős builds: pass.
- Current verdict: **PASS**.

The corrections discharge the former topology, provenance, executable-choice,
producer-to-consumer contract, and work-accounting failures.  Node `[144]` is
now a legitimate unconditional collision classifier on the
overload/homogeneous branch.  Its white semantic consumer may remain
unfinished: the local producer is green because it produces and transports
every field promised on its outgoing edge.

## Corrected branch reconstruction

The literal predecessors `[140]`, `[142]`, and `[143]` already carry an exact
overload and its indexed homogeneous matching/star audit.  The corrected
`CoarseBottleneckClassification` is parameterized by precisely those values.
It neither reruns `coupledClassDecision` nor constructs a replacement
homogeneous audit.  It has no `quadraticSpine` constructor.  Node `[138]`
therefore remains the sole no-overload/capacity consumer.

| Incoming datum | Producer | Consumption at `[144]` | Verdict |
|---|---|---|---|
| overload witness | CT9 classwise decision | exact dependent parameter | pass |
| routed overload | typed route indexed by that witness | appears in the homogeneous-audit type | pass |
| homogeneous list | `[140]/[142]/[143]` audit | exact dependent parameter | pass |
| list length 49 / nodup | homogeneous-pattern API | used locally | pass |
| code universe 48 | graph coarse-code API | used locally | pass |

`VerifiedGeometricBottleneckClassificationPrefix.classification` accepts an
overload and homogeneous audit of exactly the predecessor-indexed type.  This
is sufficient to apply it to every actual output of `previous.audit`; it no
longer recomputes a logically unrelated branch outcome from `ctx`.

## Executable classifier and quantifier audit

`verifiedCollision` generalizes the actual
`Core.FiniteCodeCollision.decide` result.  Its `.collision` case retains
`decisionExact`; its `.unique` case is eliminated by the 48-versus-49 bound.
Distinctness is derived from nodup of the exact pattern list, and code equality
comes from the computed ordered collision.  The collision itself is not
proof-selected.

The classifier asserts no attachment alignment, response equivalence,
separating context, smaller representative, sparse exit, Type-B entry, or
near-cubic conclusion.  `StructuralAttachmentMaps` stores the two literal
maps independently, and `CanonicalGermResidual.requiredAlignment` names the
open proposition without supplying a proof.  The pendant-leaf countermodel to
the old semantic implication therefore does not refute this local theorem.

## Producer-to-white-consumer contract

The corrected graph API registers `SemanticBottleneckTrigger` as the exact
input type of the unique downstream semantic bottleneck consumer.

- S-Rout is `toSemanticBottleneckTrigger`.
- S-Trig is `semanticBottleneckTrigger_total` and requires no alignment
  hypothesis.
- Persistence is `semanticBottleneckTrigger_source_exact`; the identical
  collision, attachment maps, and canonical germs are retained.
- The open goal is definitionally identified with `AttachmentAlignment` and
  is not carried as a proof field.
- The Erdős `CoarseBottleneckClassification` stores the constructed trigger,
  so the outgoing edge is executed rather than merely described in prose.

This is a legal green-producer/white-consumer boundary.  The review rule judges
node completeness locally and explicitly allows consumers of a node's outputs
to remain unfinished.  The later white consumer must still refine attachment
mismatch, parallel germs, cubic/high-separator cases, and endpoint failure;
none of those semantic conclusions may be attributed to `[144]`.

## Both-sides and leaf-total audit

There is now one leaf on the active branch:

| Leaf | Progress | Typed endpoint | Verdict |
|---|---|---|---|
| actual first equal-coarse-code pair | strict finite refinement of the 49-entry homogeneous list | `SemanticBottleneckTrigger` | pass |

The no-overload leaf is not part of this node and is not required here.  There
is no hidden alternative or caller hypothesis restating the classification.
The handoff is acyclic at this frontier because the consumer is later and
white; no return edge is claimed.

## Transfer and trust

The new `Fin 49 -> Fin 48` fixture is theorem-independent and executes the same
Core decision kernel.  `fixtureDecision_is_collision` retains an equality to
the actual result and rules out `.unique` by finite cardinality.  This is an
adequate transfer for the collision kernel; the graph-indexed producer remains
separately exercised by the generic framework theorem.

Focused builds passed for:

- `StructuralExhaustion.Core.FiniteCodeCollision`;
- `StructuralExhaustion.Graph.SurplusPatternCoarseRouting`;
- `StructuralExhaustion.Examples.SurplusPatternGermAudit`; and
- `Erdos64EG.CT10GeometricBottleneckClassification`.

No `sorry`, `admit`, or additional external mathematical axiom was found in
the implicated files.  The complete Erdős prefix retains the sole declared
HSS trust dependency, in addition to ordinary Lean axioms.

## Local work audit

`classificationWork` now charges the conservative envelope

```
3 * length^2 + 2 * zstarBudget
```

The executed Core runner does not cache codes.  At each nested-list test it
evaluates the predicate

```
code first = code second
```

through `FiniteSearch.onList`, so both `code first` and `code second` may be
reevaluated at every comparison.  The first `length^2` term pays for all pair
comparisons and the remaining `2 * length^2` pays for those two uncached code
projections per comparison.  The two selected rooted germs are charged by the
two `zstarBudget` terms.  This safely covers the current execution model without
assuming compiler sharing or a precomputed code table.

At the fixed node-`[144]` length 49, the theorem reduces this envelope to
`7203 + 2 * zstarBudget`: 2401 comparisons and at most 4802 coarse-code
projections, plus the two germ/BFS budgets.  The generic and Erdős statements
use the same units and formulas.

The two selected germ budgets are now present.  `zstarBudget` is explicitly a
static polynomial envelope rather than an instrumented runtime count; that is
acceptable if the theorem consistently calls the whole result a conservative
work envelope rather than an exact operation trace.

## TeX--Lean scope

The source manuscript was intentionally not edited during this re-audit and
its hash is unchanged.  TeX/web synchronization, dependency redirection, and
formalized-node registration remain integration work after a PASS.  The old
sparse-exit/Type-B closure must stay assigned to the white semantic consumer,
not to this green classifier.

## PASS disposition

- No blocking, required-cleanup, quantifier, branch, provenance, route,
  practicality, transfer, or trust finding remains for the local classifier.
- Node `[144]` may be integrated as a green fixed coarse bottleneck
  classifier, with the semantic sparse-exit/Type-B consumer remaining the next
  white frontier.
- The old semantic closure and its global consequences must not be marked
  proved by this PASS.
- No TeX or web integration was performed by the red-team audit.

**Final verdict: PASS.**
