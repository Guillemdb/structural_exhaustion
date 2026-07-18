# Node [144]: open--open endpoint-failure contract

## Original manuscript route

The retained failure has one of the two forms

- the first port endpoint belongs to the second port's shoulder pair; or
- the second port endpoint belongs to the first port's shoulder pair.

Both ports are already proved open.  This is exactly a blocker of type (c) in
`def:surplus-blockers`: the same literal vertex occurs as the cubic buffer of
one port and as a shoulder of the other.  It is not a compatible-pair Type-B
entry.

The paper also attaches the single-open-port response of
`lem:single-open-port-suppression-witness` to every active open demand.  For
the port whose shoulder pair contains the foreign endpoint, suppress its cubic
endpoint and add its absent shoulder chord.  Minimality supplies a target
cycle in the suppressed graph.  Target avoidance forces that cycle to use the
added chord.  Removing the chord gives the exact simple shoulder-to-shoulder
path in the source graph, avoiding the suppressed endpoint, with accepted
successor length.

## Finite local classifier

The shoulder list has length two.  The classifier therefore has four exact
outcomes:

1. first endpoint = first shoulder of second port;
2. first endpoint = second shoulder of second port;
3. second endpoint = first shoulder of first port;
4. second endpoint = second shoulder of first port.

Each outcome records:

- the foreign and suppressed raw ports;
- both exact open proofs;
- their distinctness;
- which of the two literal shoulders is the foreign endpoint; and
- the shared buffer/shoulder carrier.

No vertex, path, graph, context, or response universe is scanned.  The only
runtime distinction is membership in the already proved two-element shoulder
list.

## Lean bridge

`Graph/HighOpenEndpointFailure.lean` should provide:

- `NormalizedFailure` and its four-case `classify`;
- a raw-port `OpenPortSuppression.Setup` derived from the suppressed open port;
- `SharedCarrier`, proving the exact buffer/shoulder coincidence;
- `ActivatedFailure`, retaining the proof-selected critical suppressed cycle
  and its extracted predecessor path; and
- an activation constructor from the existing minimal-counterexample and
  minimum-degree-three hypotheses.

The node-[144] root and after-edge adapters may consume the
`OpenEndpointFailure` constructor already returned by the detailed separator.
They must retain the complete separator provenance.

## Smallest unresolved residual

The local shared carrier and suppression response are derivable.  What is not
derivable from the detailed separator is that either raw port belongs to the
chosen excess selector or the verified active-demand schedule.  Therefore the
global blocker ledger cannot yet be invoked.  The residual is:

> an activated literal type-(c) shared carrier, waiting for selected-slot
> provenance identifying the two raw ports with active surplus demands.

No Type-B assignment and no ambient-context response equivalence may be
inferred on this branch.
