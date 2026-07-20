# Node [31] wedge conditional-fibre contract

Status: specification sketch only. This file does not modify the manuscript
and does not claim that the lemma below has been proved.

## Fixed diagram position

This contract strengthens only the mathematical payload produced at node
`[31]`. It introduces no node, edge, case, or residual family. Its input is the
literal residual on the existing

```text
[30] -> [31] -> [32]
```

path. Node `[32]` retains exactly its printed rank-drop/full-rank dichotomy.
Node `[48]` is the first consumer of the additional full-fibre certificate.

## Incoming residual data

Write `B31` for the exact branch residual received from node `[30]`. The
following objects are views of data already owned by `B31`; they are not new
families constructed at node `[31]`.

1. `States(B31)` is the finite ordered carrier of compatible hot residual
   states. Its order, duplicate-freeness, and realization semantics come from
   the accumulated framework ledger.
2. `Wedges(B31)` is the finite ordered carrier of internal length-two
   remainder wedges constructed at nodes `[29]`--`[30]`.
3. For `w in Wedges(B31)` and `s in States(B31)`, `triple(w,s)` is the legal
   label triple `(S,A,T)` read from the same residual state at the three
   vertices of `w`.
4. `safe(w,s)` says
   `C1(S,A)=C1(A,T)=1` for `triple(w,s)`.
5. `flat(w,s)` says `safe(w,s)` and `Omega2(S,A,T)=0`.

The semantic projection `triple` must be defined by the graph layer. It must
read the existing residual state and must not enumerate graphs, completions,
contexts, label assignments, or a replacement state carrier.

The node-[21] finite table supplies the exact constants

```text
safeCount = 543958,
flatCount = 111286.
```

## Prefix fibres

Let `I = (w_0,...,w_{r-1})` be the ordered surviving wedge schedule selected
by node `[31]` from `Wedges(B31)`. Define, through the generic Core
conditional-fibre view of the incoming carrier,

```text
F_0     = States(B31),
F_{i+1} = {s in F_i | flat(w_i,s)}.
```

These are successive filtered views of the one incoming carrier. They are not
application-owned families or new residuals.

## Local switching certificate

For every `i < r`, a **prefix-preserving wedge switch** is a framework-owned
finite injection

```text
switch_i : F_{i+1} x Fin 543958 -> F_i x Fin 111286.
```

Its graph-specific semantic proof must establish all of the following.

1. The source and target states are literal members of the displayed prefix
   fibres of `States(B31)`.
2. The switch modifies only the declared local response data of `w_i`.
3. It preserves the fixed remainder, every packed-window choice, every
   compatibility condition, and the flat outcomes of `w_0,...,w_{i-1}`.
4. Its first component has the legal-label triple represented by its finite
   index.
5. Equality of switched states and reconstruction indices recovers the source
   state and safe-label index; hence `switch_i` is injective.

Finite cardinality of this injection gives exactly

```text
543958 * |F_{i+1}| <= 111286 * |F_i|.
```

This injection is a proof device. Core may equivalently accept the displayed
inequality together with its semantic certificate, but the Erdős layer must
not assert the inequality without the switch/recovery proof.

## Terminal realization

A **terminal flat realization** is a literal state `s* in States(B31)` such
that

```text
forall i < r, flat(w_i,s*).
```

It proves `F_r` is nonempty. The witness must come from the incoming residual
ledger. It may not be a caller-supplied state or a newly constructed global
completion.

## Strengthened node-[31] lemma

> **Lemma (full target rank carries a conditional wedge-fibre ledger).**
> Let `B31` be the literal node-[30] residual. Let `I` be the ordered maximal
> subfamily of raw remainder wedges surviving the functional admissible
> quotient system used to define `r_Omega(R)` at node `[31]`. Then the graph
> projection `triple` and the exact node-[21] safe/flat table determine a
> `Core.ConditionalFibreRank.Profile` on the literal carrier `States(B31)` and
> coordinate schedule `I`. Its execution has the following interpretation:
>
> - a failed conditional step produces the existing node-[32] rank-drop
>   outcome, with its first failed wedge and the corresponding determination
>   certificate;
> - on the node-[32] full-rank outcome, every prefix-preserving wedge switch
>   exists and there is a terminal flat realization.
>
> Consequently the full outcome contains a
> `ConditionalFibreProductCost.CertifiedCarrierOutput` with safe count
> `543958`, flat count `111286`, coordinate length `|I|`, and state count equal
> to the cardinality of the exact incoming residual state carrier.

No failure is discarded. The statement identifies failure of the conditional
fibre run with the rank-drop edge already present at node `[32]`; proving that
identification is part of the lemma, not a definition.

## Immediate consequences owned by the framework

For the full outcome, Core telescopes the prefix inequalities and uses terminal
nonemptiness to obtain

```text
543958 ^ |I| <= 111286 ^ |I| * |States(B31)|.
```

Node `[49]` later names the cardinality of this same carrier `stateCount`; it
must prove carrier identity by retrieving the node-[31] view, not by defining a
second state family. Thus node `[48]` can attach the equivalent statement

```text
543958 ^ |I| <= 111286 ^ |I| * stateCount.
```

On the full-rank branch, node `[32]` identifies `|I|` with the curvature target
rank (and, under its exact zero-loss threshold, with the raw wedge count).
The framework's powered-budget composition then combines this certificate
with node `[50]`'s strict-low comparison and closes node `[53]`'s small edge at
node `[54]`.

## Proposed Lean ownership

The eventual implementation must have the following ownership split.

- `Core`: filtered prefix fibres, finite injection/cardinality conversion,
  conditional-fibre execution, telescoping, terminal nonemptiness, powered
  budget composition, and accumulated-ledger attachment.
- `Graph`: projection of one literal residual state to the legal label triple
  of one literal wedge; preservation and recovery laws for a local wedge
  switch.
- `CT15`: the first-failure/full-rank result and the theorem identifying a
  failed conditional step with the existing rank-drop payload.
- Erdős node `[31]`: only the fixed safe/flat predicates, the exact constants,
  and the thin instantiation on its incoming residual.
- Erdős node `[48]`: no new carrier or telescope; it retrieves the full
  certificate and records the paper's cost-unit reformulation.

## Proof obligations to discharge before implementation is green

1. `triple` is well-defined on every incoming residual state and wedge.
2. `safe(w,s)` holds on the relevant pre-fibre states.
3. Every `switch_i` is total on `F_{i+1} x Fin 543958`.
4. Every `switch_i` remains inside `F_i` and preserves the earlier prefix.
5. Every `switch_i` has a recovery map proving injectivity.
6. A failed switching/conditional step constructs the exact functional
   rank-dependence payload consumed by node `[32]`'s existing yes branch.
7. The full branch supplies a terminal flat realization from the incoming
   residual.
8. The initial fibre is definitionally, or by a framework-certified exact
   view, the state carrier counted at node `[49]`.
9. All checks are local in `|States(B31)| * |I|`; no ambient graph or completion
   universe is enumerated.

Until obligations 1--9 are proved, this file remains a specification and node
`[31]` must not be marked green on the strengthened contract.
