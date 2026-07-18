# Node [84] unconditional global-realization blocker

Date: 2026-07-17

Status: the local node-[84] routes and the canonical ordinary component family
are kernel proved.  An unconditional
`Node84GlobalFanMass.Realization node84` is not constructible from the current
Lean predecessor state because the grouped input schedule on the existing
`[108] -> [66] -> [65] -> [84]` route has no global producer.

This report adds no diagram node, edge, case, or residual.

## Dependency-ready facts

- `TypeBEntryRouting.node64` constructs one ordinary node-[64] residual from
  one supplied node-[61] support and its actual high-center witness.
- `TypeBEntryRouting.VerifiedNode65Residual.ordinary` and `.decorated` preserve
  the occurrence's exact branch tag and source.
- `TypeANodes107To108Handoff.VerifiedNode107Residual.node108` constructs one
  exact decorated handoff from one supplied node-[107] residual.
- `Node84GlobalFanMass.CanonicalOrdinary.family` is a graph-owned finite scan
  of the canonical remainder-component order.  It proves exact coverage of
  its eligible ordinary components, occurrence identity, within-ordinary-role
  center injectivity, and the coefficient-208 bound.
- `Node84GlobalFanMass.verify` proves the factor-416 CT14 conclusion from a
  completed `Node84GlobalFanMass.Realization`.

## First missing producer

There is no finite graph-owned schedule of all actual node-[107] survivors or
node-[108] exit-(7) handoffs.  Tracing this dependency backward reaches node
[93]: `TypeANode89SaturationDecision` computes an actual saturated receiver,
but `TypeANode93VisibleFamily.VerifiedNode93Residual` still receives its
visible-return schedule and declared response fields from the caller.  Thus no
finite branch runner owns the occurrences on which nodes [95]--[107] operate.

The existing `node108` declaration is only a local constructor:

```text
one supplied VerifiedNode107Residual -> one exact Exit7Handoff
```

It does not imply:

```text
one finite list containing every actual exit-(7) handoff, with exact coverage
```

Without that list Lean cannot form the manuscript's finite core--center
incidence graph, compute its connected components, or construct the grouped
decorated support schedule.  In particular, using an empty grouped schedule,
a caller-supplied schedule, or one singular handoff would fail the required
coverage theorem.

## Consequent unresolved `Realization` fields

The absent grouped schedule blocks these fields of
`Node84GlobalFanMass.Realization`:

1. `GroupedFamily`, `groupedFamilySchedule`, and
   `canonicalGroupedSource`, with exact occurrence coverage;
2. the grouped support map and injectivity/disjointness facts;
3. `groupedOccurrenceExact` and within-grouped-role center injectivity, which
   require the complete incidence-component partition;
4. `groupedCoefficient208IncidenceBound`, whose proof must use the complete
   grouped envelope rather than a single handoff incidence; and
5. the complete ordinary/grouped support schedule and hence the unconditional
   `Node84GlobalFanMass.Realization` constructor.

The next valid implementation step is therefore the existing manuscript
route's graph-owned node-[93] visible-return/declared-response producer,
followed by the sequential node-[95]--[107] branch runner, the node-[108]
handoff schedule, and finally the local finite incidence-component scan.  Each
scan must enumerate only its produced predecessor occurrences, never ambient
paths, vertex subsets, contexts, or possible supports.
