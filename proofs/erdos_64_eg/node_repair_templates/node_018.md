# Node [18] repair template

| Field | Value |
|---|---|
| Incoming | [17] -> [18] |
| Outgoing | [18] -> [19] |
| Responsibility | Build the P13 label algebra: 399 labels, relations C_s, curvature Omega_2. |
| Retained facts | Literal maximal packing and prior ledger. |
| New output | Exact label/relation/curvature certificate. |
| CT chain | CT10 finite classification successor. |

| Task | Assertion | Producer | Evidence | Status |
|---|---|---|---|---|
| N18-PRED | Consume literal Node17Stage and its live graph cursor | [17] | `Node18Stage`; `Node17StageContext`; `node18P13LabelAlgebra`; `runInitialThroughNode18` | proved; kernel checked |
| N18-LABELS | Certify 399 labels and all seven size fibres | [18] | `Core.FiniteWeightedAutomaton`; `P13ParityLabelCount.gapSafeSized13_natCard_eq_convolution`; `P13ParityLabelCount.gapLegal13_natCard`; `legalP13LabelEquivGapLegal`; `p13LegalLabel_count`; `p13LegalLabel_size_distribution`; `Node18Output.labelCount`; `Node18Output.sizeDistribution` | proved; kernel checked |
| N18-REL | Certify all C_s relations | [18] | `Node18Output.relationSemantics`; `p13C_eq_one_iff` | proved; kernel checked |
| N18-CURV | Construct Omega_2 curvature | [18] | `Node18Output.curvatureSemantics`; `p13OmegaTwo_eq_one_iff` | proved; kernel checked |
| N18-ACTUAL | Prove every actual outside-neighbour label is legal on the literal node-[17] graph | [18] | `Node18Output.actualLabelsLegal`; `attachmentLabel_legal_of_avoids` | proved; kernel checked |
| N18-CERT | Retain CT10 trace/semantics/work | CT10 | `Node18Output.classificationStage`; `p13Label_candidate_count`; `node18LocalChecks_eq`; generic CT10 trace, semantics, totality, and polynomial certificate | proved; kernel checked |

Forbidden: nested packing prefix or copied predecessor equality.

Current repair status: **proved and kernel checked**.  The literal successor, CT10 exhaustive stage,
actual-label legality, exact `399` count, all seven size fibres, `C_s`, and
`Ω₂` are attached to the single accumulated ledger.  The count is transported
symbolically from the two parity automata; neither the total nor the fibre
distribution scans the `8192` ambient codes.  The shallow legal carrier
`symbolicLegalP13Labels` and its `Fin 399` index are available to later local
tables.
