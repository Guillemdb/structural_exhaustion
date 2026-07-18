# Node [84] original-contract audit

Status: **yellow**.  The exact local incoming-edge payloads are kernel proved,
but the original single-node global fan-mass output to `[85]` does not yet have
an upstream producer.  This audit does not change the Chapter 1 diagram,
manuscript prose, WebExport status, or any public branch outcome.

## Immutable directed contract

The original Part VII diagram has exactly these routes relevant to `[84]`:

```text
[80] certificate absent ----------------------> [84]
[80] certificate present -> [81] unresolved --> [84]
[80] certificate present -> [81] B2 failure
                         -> [83] overlap ------> [84]
[84] ------------------------------------------> [85]
```

The successful full-choice alternatives through `[82]` retain their existing
nonnegative or route-8 payloads and are not new `[84]` inputs.  No additional
case, edge, node, or outcome is admitted.

## Kernel-proved local handoffs

`Erdos64EG.CT14TypeBLocalFanMass` now exposes three theorem-only connectors:

| Incoming edge | Lean theorem | Exact selected centers |
|---|---|---|
| `[80] -> [84]` | `certificateFailure_localFanMass` | the literal failed center singleton |
| `[81] -> [84]` | `unresolved_localFanMass` | the concrete center whose certificate-tied local-entry fibre is empty |
| `[83] -> [84]` | `minimalOverlap_localFanMass` | the duplicate-free center set of the literal minimal-overlap obstruction |

Each connector invokes `TypeBSupportScope.localFanMass` on data already
contained in its predecessor.  The reusable CT14 profile scans only the
scope's actual finite high-center schedule.  It proves the exact selected
cardinality, equality with the scope's assigned-surplus ledger, the local
charge bound, and a quadratic local work bound.  No graph family, vertex
subset family, or ambient universe is enumerated.

Focused verification:

```text
lake build Erdos64EG.CT14TypeBLocalFanMass
Build completed successfully (3232 jobs).
```

## One exact missing producer

The missing object is a **canonical global ordinary/grouped support-family
producer descended from the existing decomposition and exit-(7) handoffs**.
It must compute the one actual finite support and occurrence schedule consumed
by `Graph.SupportIndexedFanMass`, while proving all of the following as parts
of that single producer:

1. every retained ordinary node-`[84]` residual and every grouped decorated
   exit-(7) envelope occurs exactly with its existing provenance;
2. each non-extracted support's literal deficit satisfies the corrected
   coefficient-`208` processed-envelope bound using its recorded center
   occurrences;
3. center occurrences are injective within the ordinary role and within the
   grouped role, so each ambient surplus unit is used at most twice; and
4. every extracted ordinary support carries its exact existing route-8
   non-window core.

These are not four independent frontier branches.  They are the semantic
fields of one graph-owned canonical-family producer required to instantiate
the already verified support-indexed CT14 aggregation.  The current
`VerifiedTypeBLocalFanMassPrefix` is universally quantified over a *supplied*
scope; it does not enumerate the canonical scopes.  The existing exit-(7)
connector records one supplied handoff at a time; it does not prove coverage
of the canonical grouped family.  A repository search finds no constructor of
`Node84GlobalFanMass.Realization` or `TypeBGlobalFanMassProducer`, only their
conditional consumer contracts.

Consequently the generic theorem

```text
residualMass <= 416 * globalSurplus
```

is available once that producer exists, but invoking it now would assume the
original node-[84] conclusion rather than derive it from `[80]`--`[83]`.
Therefore `[84]` cannot honestly be colored green and the outgoing `[84] ->
[85]` global mass handoff remains unconstructed.

## Synchronization decision

The focused Lean module builds, but the full original node contract does not.
Accordingly `proofs/erdos_64_eg/erdos_64_proof.tex` and `WebExport.lean` are
left unchanged.  The live TeX SHA-256 observed before and after this audit is
`c92afa242859afd46ac0c8859b220a97a0b62e4f27654824c84731f071855de5`;
the diagram topology is untouched.

## 2026-07-17 producer follow-up

The ordinary half of the producer is now graph-owned.  Module
`Erdos64EG.CT14TypeBCanonicalOrdinaryFamily` filters the one canonical
remainder-component order by the exact node-[84] branch conditions (negative
charge, no center above degree four, and center-deleted unsaturation).  It
provides exact family and center-occurrence enumerations, component coverage,
source provenance, within-ordinary-role center injectivity, and derives the
coefficient-208 bound from the proved coefficient-21 quarter-charge theorem.
`P13ProducedPriorSupportLedger.canonicalOrdinaryLedger` records every such
entry in that exact order.

The remaining grouped dependency lies on the original edge `[108] -> [66]`.
The current Lean tree has no node-[108] producer theorem: the only declaration
named `Exit7Handoff` is the expected handoff type, and `node66AndRecord`
correctly records one already supplied value.  There is no compiled execution
of nodes `[95]`--`[108]` that produces the finite pairwise-disjoint Type-A core
family or proves that its list contains every surviving exit-(7) handoff.
Consequently the grouped incidence-component schedule cannot be derived
without supplying precisely the missing node-[108] conclusion.  This is an
absent producer on an existing edge, not grounds for an additional diagram
case or residual.

There is a second, specification-level obligation inside the same existing
edge.  `CT14TypeBGlobalFanMass.GroupedExitSevenEnvelopeSource` presently
stores one core, one handoff, and one center.  It is only a single produced
incidence, not the grouped support of
`def:decorated-typeB-envelope-support`.  The manuscript groups the complete
finite core--center incidence graph by connected components, deduplicates all
cores and all centers inside each component, and charges each center token
once.  The final node-[84] realization must therefore be built from those
actual incidence components; using the current singular record as the grouped
family would be an invalid specialization.  This is payload still missing on
the original `[108] -> [66] -> [84]` flow, not a new node or branch.
