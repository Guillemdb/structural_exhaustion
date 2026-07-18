# Red-team audit: node [144] high-compatible origin

## Verdict

The implemented bridge is locally sound and deliberately stops before the
unproved Type-B assignment.  It does not yet complete node [144].

## Quantifier and provenance checks

1. **Raw-port identity is preserved.**  `OpenCompatibleOrigin.firstPort` and
   `secondPort` are subtypes of the exact recovered ports, with definitional
   projection equalities.  No fresh neighbour or port is chosen.
2. **Compatibility is not confused with openness.**  The incoming
   `FanCompatible` proof is refined by the exact four-case port-type table.
   Only `openOpen` constructs the ordinary compatible-open-pair origin.  The
   three other cases retain their exact type equalities in
   `TriangularCompatibleResidual`.
3. **No assignment is inferred from activity or compatibility.**
   `AssignmentFrontier` contains only the proved open origin.  Its consumer
   `AssignedEntry` separately requires an actual `FanWindowProfile` and an
   `AssignedPair`.
4. **No arbitrary universe is searched.**  The only classifier is
   `classifyPairCase`, a fixed two-port/four-case split.  The carrier list has
   exactly four literal incidences.
5. **The root and after-edge sources are not conflated.**  Separate adapters
   retain `RootHighData` and `AfterEdgeHighData`; the predecessor/third-port
   incidence data therefore remain available downstream.

## Failed stronger claims

The following claims cannot be obtained from the current node-[144] source:

- either open endpoint belongs to `p13RemainderVertices`;
- either endpoint belongs to a connected localized support core;
- any of the four shoulder carriers is assigned by induced-core adjacency;
- the common center is recorded in an admissible Type-B profile;
- a decorated handoff core `Y`, handoff arms, terminal coordinates, or a
  fan-safe clique exists.

All five require semantic data absent from
`SurplusPatternDetailedSeparator.RootHighData` and
`AfterEdgeHighData`.  Importing `TypeBFanWholePortAssignment` would not repair
this: its constructors require `VerifiedNode64Residual`, and no route from the
node-[144] germ residual to that exact residual is currently proved.

## Minimal residual

The remaining residual is the open-compatible `AssignmentFrontier` plus the
obligation to construct its `AssignedEntry` from graph-owned packing/support
data.  This residual is minimal in the following sense:

- deleting the origin loses the exact raw ports and carrier identities;
- deleting the `FanWindowProfile` from the consumer loses the manuscript's
  window/remainder semantics;
- deleting `AssignedPair` loses exactly the two endpoint and four incidence
  hypotheses used by `lem:compatible-pair-fan-closure`.

The next repair must either derive that entry directly from the current
surplus branch or prove a typed route to the earlier node-[64] residual.  A
profile with predicates chosen merely to make the obligations true is not an
acceptable repair.
