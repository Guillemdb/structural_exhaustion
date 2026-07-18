# Erdős--Gyárfás 64 Part IV original-flow blocker

## Scope and immutable topology

This audit covers the original Chapter 1 chain

```text
[47] -> [48] -> [49] -> [50]
                     yes -> [51] -> [52] -> [54]
                      no -> [53] --yes------> [54]
                                   no-------> [55] -> [56]
```

The authority is `original_erdos_64_proof.tex`.  In particular, there is no
edge from `[48]` to `[55]`, no realized/open decision at `[48]`, and no
realized/open decision at `[52]`.  Such alternatives may describe an audit
failure internally, but they are not manuscript outcomes and cannot be used
as public Lean proof flow.

## Sequential dependency audit

| Node | Exact original responsibility | Required predecessor | Current Lean evidence | Verdict |
|---|---|---|---|---|
| `[31]` | Define curvature target-rank by a subfamily realizing all `2^k` target-response states | exact wedge coordinates from `[30]` | `CT15.AdmissibleQuotient` rules out pairwise label identification by an admitted quotient | **not equivalent; demote** |
| `[32]` | Decide whether that realization rank drops | original node-`[31]` rank | CT15 decides its weaker quotient-identification predicate | **blocked by `[31]`** |
| `[33]`--`[46]` | Route an actual rank drop through the existing target-defect, compression, and delocalization exits | original node-`[32]` rank-drop witness | typed conditional consumers exist, but the missing-response-pattern witness is not converted to one of them | **conditional support only** |
| `[47]` | Conclude full curvature target-rank after every rank-drop exit closes | original nodes `[31]`--`[46]` | equality of the CT15 coordinate count with the wedge count | **weaker than original; demote** |
| `[48]` | Charge the full realized curvature rank at rate `c_\Omega` and pass the unique result to `[49]` | `[47]` and the same-context node-`[24]` density handoff | exact wedge/surplus arithmetic plus a caller-supplied conditional-fibre realization | **blocked; no original open edge** |
| `[49]` | Entropy of the actual node-`[48]` realized state family | unconditional `[48]` output | correct bookkeeping only after a supplied realization | **blocked by `[48]`** |
| `[50]` | Exact high/low comparison for the node-`[49]` count | `[49]` | correct conditional arithmetic | **blocked by `[49]`** |
| `[51]` | High-branch logarithmic bit lower bound | high edge of `[50]` | correct conditional arithmetic | **blocked by `[50]`** |
| `[52]` | Joint window--remainder accounting that bounds `theta` | `[51]` | only a caller-supplied joint realization or its absence | **blocked; absence is not an original edge** |
| `[53]` | Test the remaining non-curvature budget on the low edge of `[50]` | low edge of `[50]` | symbolic inequality transport after a supplied node-`[48]` ledger | **blocked by `[48]`--`[50]`** |
| `[54]` | Close both incoming entropy-cap branches | `[52]`, or the yes edge of `[53]` | no unconditional closing theorem | **blocked** |
| `[55]` | Retain the no edge of `[53]` as the large-budget residual | no edge of `[53]` | a separate quarter-budget interface is available, but is not produced by `[53]` | **blocked** |
| `[56]` | Prove the strict quarter net-deficiency cap | `[55]` | exact arithmetic from a caller-supplied quarter budget | **blocked by `[55]`** |

Node `[24]` is independently yellow and is also an incoming blocker for the
same-context finite estimates at `[48]`.  Even after `[24]` is completed, the
rank-semantics defect above remains.

Under the repository's whole-node green policy the exact demotion set is
`[31]`--`[47]` inclusive.  Nodes `[33]`--`[46]` retain useful conditional
lemmas, but their displayed original responsibilities require an incoming
rank-drop value produced from node `[32]`; accepting an author-supplied
certificate is not unconditional predecessor provenance.  Node `[30]` is the
last unconditional original-flow endpoint on this lane.  Nodes `[48]`--`[56]`
are already non-green and must remain so.

## The false implication

The original definition of target rank uses simultaneous realization:

```text
rank >= k  means  every Boolean response vector on k coordinates is realized.
```

The current CT15 specialization proves instead:

```text
every admitted response-preserving quotient code is injective on the labels.
```

The second statement does not imply the first.  This is already proved inside
Lean by

```text
StructuralExhaustion.Examples.BooleanStateEntropy.
  responsePreservingInjectivity_does_not_realize_cube
```

on the three response states `00`, `01`, and `10`.  Every
response-preserving label code is injective, and each individual coordinate
takes both values, but the joint state `11` is absent.  Therefore the failure
cannot be repaired by a generic rank or injectivity lemma.

## Exact missing graph lemma on the existing edges

To retain the original strategy and topology, the missing producer must be a
graph-specific theorem with the following responsibility:

1. inspect only the actual finite graph-completion states and the declared
   curvature coordinates on the selected remainder;
2. if every response vector is realized, return the original node-`[47]`
   full-rank payload used by `[48]`;
3. if a response vector is missing, construct an actual functional
   determination certificate whose support is routed through the already
   existing node-`[32]` yes edge and nodes `[33]`--`[46]`;
4. prove that the target-defect, proper-replacement, proper-delocalization,
   and whole-support alternatives produced are exactly the existing Part II
   and Part III outcomes.

Equivalently, the missing implication is not “injectivity implies a Boolean
cube.”  It is the graph-semantic statement that every omitted response vector
forces one of the manuscript's existing compression/rank-drop certificates.
No theorem with that conclusion is currently present.  It requires a closure
or exchange property of the actual graph-completion family; arbitrary finite
response systems do not have it.

The proof must use proof-selected local completion data or a locally checked
extension schedule.  Enumerating all labelled graphs, all outside contexts,
or the Boolean cube is not an admissible implementation.

## Quarantine decision

The declarations currently named `P13Node48Outcome.openRequirement` and
`P13Node52Outcome.openRequirement`, and their conditional routes to a
quarter-budget consumer, are audit interfaces rather than original proof
outcomes.  They must not justify green status, appear as directed proof
edges, or supply `[55]`.  The only legal Part IV entrance to `[55]` is the
original no edge of `[53]`.

The finite wedge identities, state-count bookkeeping, power comparison,
logarithmic transfer, product-capacity arithmetic, and strict-quarter
arithmetic remain useful support lemmas.  They become node implementations
only after the unique original predecessor payloads above are produced.
