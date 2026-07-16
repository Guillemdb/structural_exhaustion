# Node 177 semantic-bottleneck classifier: red-team audit

## Reopened residual

The input is the canonical `SemanticBottleneckTrigger` produced by node 144.
The Erdős instantiation uses `coarseBottleneckClassification` itself, not an
arbitrary inhabitant of its result structure.  Consequently the trigger's
`source` is definitionally the exact canonical germ residual, and the same
collision, attachment maps, and two retained BFS germs persist.

## Finite universe and execution

The only new search universe is

`WindowIndex × Fin 13 × Bool × PortRole`.

It has exactly `78 * packingNumber` coordinates.  These are the already
selected CT12 windows, their 13 positions, the two collided-pair slots, and
the three fixed port roles.  The scan does not enumerate ambient vertices,
graphs, paths, embeddings, attachments, or homogeneous-pattern pairs.  At
each coordinate it compares the two retained executable adjacency maps and
returns either the first mismatch (with its clean prefix) or a proof of map
alignment at every declared coordinate.

CT10 separately scans the complete five-tag candidate alphabet and accepts
exactly the tag computed by the alignment/germ classifier.  The accepted
table therefore has one class, its exact reference cost is `5 + 1 + 1 = 7`,
and the combined charged work is `234 * packingNumber + 7`, bounded by
`234 * |V| + 7`.

## Leaf audit

There are exactly five typed leaves:

1. first attachment-map mismatch;
2. aligned maps with the first germ a prefix;
3. aligned maps with the second germ a prefix;
4. aligned maps with divergence at the root;
5. aligned maps with divergence after a retained edge.

The mismatch leaf preserves an actual first-hit witness.  Each aligned leaf
preserves the computed full alignment proof and an equality to the shape of
the already retained BFS comparison.  No leaf asserts sparse exit, CT3
compression, Type-B structure, fixed-cap closure, or a target cycle.  Those
remain explicit downstream white consumers.

## Adversarial checks

- **No injected alignment:** alignment is constructed only from exhaustive
  absence of a mismatch in the declared coordinate enumeration.
- **No ceremonial CT10 table:** `Profile.exactSelection` ties the accepted
  CT10 class definitionally to the actual computed residual tag.  The Erdős
  result stores the verified CT10 stage, an equality to the actual residual,
  and the proof that this residual is the accepted class.
- **No quantifier weakening:** enumeration completeness converts the absence
  proof back to all windows, positions, pair slots, and roles, matching
  `AttachmentAlignment` exactly.
- **No branch leakage:** the source trigger is stored with an equality to the
  canonical predecessor trigger.
- **No circular semantic normalization:** germ shape is a case split on the
  predecessor's stored `TreePathComparison`; it proves no new graph fact.
- **No unsupported route:** node 144 to the finite alignment scan is ordinary
  typed theorem composition; CT10 is run on the explicit complete residual
  class table.  No new registered route is claimed.
- **Trust boundary:** focused local `#print axioms` checks report only
  `propext`, `Quot.sound`, and `Classical.choice`.  The end-to-end Erdős
  existence theorem additionally reports the repository's sole permitted HSS
  theorem.  There is no `sorryAx` or native-decision axiom.

## Verdict

The finite node-177 classifier is locally unconditional and fully
implemented.  The former global semantic conclusion is not discharged and
must remain outside this green node until one of the four aligned residual
consumers proves it.
