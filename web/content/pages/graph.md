# Graph

The Graph layer gives finite graph meaning to Core contracts. It supplies packed finite objects, isomorphism semantics, induced structures, deletion, boundaries, gluing, responses, and Graph-specific CT constructors.

## Finite objects and invariance

`Graph.FiniteObject` packages a graph with the finite enumeration and decidable adjacency needed by executable searches. Isomorphism is the canonical semantic equivalence.

## Targets and progress

Targets remain separate from graph objects. Optional progress profiles capture strict vertex or edge decrease, while target interfaces prove invariance and reflection laws once.

## Local structure

Induced supports, boundaried atoms, outside contexts, and gluing provide exact local replacement semantics. Core performs the actual coordinate transport and assembly.

## Graph CT adapters

Graph adapters turn residual-owned vertices, edges, contexts, labels, budgets, and responses into the generic CT1–CT17 inputs. Their results remain ordinary accumulated Core stages.
