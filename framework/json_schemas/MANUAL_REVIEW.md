# Mathematical author review still required

The package is structurally validated, but extraction from diagram labels cannot replace mathematical authorship. Review the following before treating it as a formal proof artifact.

## 1. Replace prose statements by exact propositions

Each node currently preserves its displayed LaTeX label and an inferred informal obligation. Add a formal-language representation or a precise theorem statement, including quantifiers, domains, hypotheses, and conclusion.

## 2. Fill typed inputs and outputs

Payload constructors have inferred payload outputs, but many ordinary nodes have empty `inputs` and `outputs` because the diagram label alone does not expose a complete signature. Populate them from the branch-state tuple, tactic signature, and preceding definitions.

## 3. Instantiate every contract

The node specifications name required contracts. A proof record must supply a structured `contractInstances` object for each required contract and actual evidence references. Contract names alone do not discharge an obligation.

## 4. Review inferred node classifications

Node types and some specialized contracts were inferred from TikZ styles, labels, outgoing degree, and manuscript terminology. Review each row of `data/node-index.csv`, especially generic `assertion` nodes and nodes with multiple outgoing edges.

## 5. Complete payload tuple components

Payload IDs and consumers were extracted from routing labels and graph reachability. Fill `payload.tupleComponents` with the exact typed tuple entries promised in the split inventory.

## 6. Prove global semantic properties

The linter checks graph consistency but cannot prove mathematical truth, response equivalence, persistence, deterministic choice, inequalities, or well-founded descent. Those remain proof obligations represented by S-* instances.

## 7. Review scope candidates carefully

A failed local construction is not automatically a scope obstruction. `A-Scope` must contain a genuine non-expressibility argument in the current proof language and a record of attempted repairs.
