import StructuralExhaustion.Canonical.CapabilityMetadata

namespace StructuralExhaustion.Canonical.CapabilityConcepts

/-! Lean-owned semantic documentation for every declaration required by the
general CT capabilities and their registered profiles.  Contract spellings
remain exact in `requirementRef`; `declarationName` always records the fully
qualified compiled declaration. -/

def ct1 : List CapabilityConcept := [
  capabilityConcept "CT1.spec.testIndex"
    "StructuralExhaustion.CT1.Spec.TestIndex"
    `StructuralExhaustion.CT1.Spec.TestIndex
    "Test index"
    r"\mathcal{I}"
    "The finite family of target tests that CT1 must consider.",
  capabilityConcept "CT1.spec.witness"
    "StructuralExhaustion.CT1.Spec.Witness"
    `StructuralExhaustion.CT1.Spec.Witness
    "Realization witness"
    r"\mathcal{W}(G,i)"
    "The type of certificates that may realize test i in the ambient object G.",
  capabilityConcept "CT1.spec.realizes"
    "StructuralExhaustion.CT1.Spec.Realizes"
    `StructuralExhaustion.CT1.Spec.Realizes
    "Realization predicate"
    r"\operatorname{Realizes}(G,i,w)"
    "The proposition saying that witness w realizes test i in G.",
  capabilityConcept "CT1.capability.tests"
    "StructuralExhaustion.CT1.Capability.tests"
    `StructuralExhaustion.CT1.Capability.tests
    "Finite test enumeration"
    r"\operatorname{tests}=\{i_1,\ldots,i_m\}=\mathcal{I}"
    "An exhaustive ordered enumeration of all test indices.",
  capabilityConcept "CT1.capability.witnesses"
    "StructuralExhaustion.CT1.Capability.witnesses"
    `StructuralExhaustion.CT1.Capability.witnesses
    "Finite witness enumeration"
    r"\operatorname{witnesses}(G,i)=\mathcal{W}(G,i)"
    "An exhaustive ordered enumeration of the witnesses for each object and test.",
  capabilityConcept "CT1.capability.realizesDecidable"
    "StructuralExhaustion.CT1.Capability.realizesDecidable"
    `StructuralExhaustion.CT1.Capability.realizesDecidable
    "Realization decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Realizes}(G,i,w)\right)"
    "Executable evidence deciding whether a proposed witness realizes a test.",
  capabilityConcept "CT1.capability.inputSize"
    "StructuralExhaustion.CT1.Capability.inputSize"
    `StructuralExhaustion.CT1.Capability.inputSize
    "Input size"
    r"n(G)\in\mathbb{N}"
    "The application-specific size measure used in CT1's complexity certificate.",
  capabilityConcept "CT1.capability.workCoefficient"
    "StructuralExhaustion.CT1.Capability.workCoefficient"
    `StructuralExhaustion.CT1.Capability.workCoefficient
    "Work coefficient"
    r"c\in\mathbb{N}"
    "The coefficient in the certified polynomial bound on exhaustive checks.",
  capabilityConcept "CT1.capability.workDegree"
    "StructuralExhaustion.CT1.Capability.workDegree"
    `StructuralExhaustion.CT1.Capability.workDegree
    "Work degree"
    r"d\in\mathbb{N}"
    "The degree in the certified polynomial bound on exhaustive checks.",
  capabilityConcept "CT1.capability.workBound"
    "StructuralExhaustion.CT1.Capability.workBound"
    `StructuralExhaustion.CT1.Capability.workBound
    "Polynomial work bound"
    r"\operatorname{checks}(G)\le c\,(n(G)+1)^d"
    "A proof that the complete CT1 search schedule satisfies the declared polynomial bound.",
  capabilityConcept "CT1.targetEncoding.code"
    "StructuralExhaustion.CT1.TargetEncoding.Code"
    `StructuralExhaustion.CT1.TargetEncoding.Code
    "Target code"
    r"\mathcal{C}(G)"
    "The profile's finite code type for witnesses of the public target on G.",
  capabilityConcept "CT1.targetEncoding.codes"
    "StructuralExhaustion.CT1.TargetEncoding.codes"
    `StructuralExhaustion.CT1.TargetEncoding.codes
    "Finite code enumeration"
    r"\operatorname{codes}(G)=\mathcal{C}(G)"
    "An exhaustive ordered enumeration of the target codes for G.",
  capabilityConcept "CT1.targetEncoding.accepts"
    "StructuralExhaustion.CT1.TargetEncoding.Accepts"
    `StructuralExhaustion.CT1.TargetEncoding.Accepts
    "Code acceptance"
    r"\operatorname{Accepts}(G,c)"
    "The proposition saying that code c is a valid target certificate for G.",
  capabilityConcept "CT1.targetEncoding.acceptsDecidable"
    "StructuralExhaustion.CT1.TargetEncoding.acceptsDecidable"
    `StructuralExhaustion.CT1.TargetEncoding.acceptsDecidable
    "Acceptance decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Accepts}(G,c)\right)"
    "Executable evidence deciding whether a target code is accepted.",
  capabilityConcept "CT1.targetEncoding.inputSize"
    "StructuralExhaustion.CT1.TargetEncoding.inputSize"
    `StructuralExhaustion.CT1.TargetEncoding.inputSize
    "Encoded input size"
    r"n(G)\in\mathbb{N}"
    "The public-target profile's size measure for G.",
  capabilityConcept "CT1.targetEncoding.workCoefficient"
    "StructuralExhaustion.CT1.TargetEncoding.workCoefficient"
    `StructuralExhaustion.CT1.TargetEncoding.workCoefficient
    "Encoded work coefficient"
    r"c\in\mathbb{N}"
    "The coefficient bounding the target-code enumeration.",
  capabilityConcept "CT1.targetEncoding.workDegree"
    "StructuralExhaustion.CT1.TargetEncoding.workDegree"
    `StructuralExhaustion.CT1.TargetEncoding.workDegree
    "Encoded work degree"
    r"d\in\mathbb{N}"
    "The polynomial degree bounding the target-code enumeration.",
  capabilityConcept "CT1.targetEncoding.workBound"
    "StructuralExhaustion.CT1.TargetEncoding.workBound"
    `StructuralExhaustion.CT1.TargetEncoding.workBound
    "Encoded work bound"
    r"|\operatorname{codes}(G)|\le c\,(n(G)+1)^d"
    "A proof that enumerating all target codes meets the profile's polynomial bound.",
  capabilityConcept "CT1.targetEncoding.encode"
    "StructuralExhaustion.CT1.TargetEncoding.encode"
    `StructuralExhaustion.CT1.TargetEncoding.encode
    "Target encoder"
    r"T(G)\Rightarrow\exists c\in\mathcal{C}(G),\;\operatorname{Accepts}(G,c)"
    "A proof that every public-target witness yields an accepted finite code.",
  capabilityConcept "CT1.targetEncoding.decode"
    "StructuralExhaustion.CT1.TargetEncoding.decode"
    `StructuralExhaustion.CT1.TargetEncoding.decode
    "Target decoder"
    r"\operatorname{Accepts}(G,c)\Rightarrow T(G)"
    "A proof that every accepted code establishes the public mathematical target.",
  capabilityConcept "CT1.targetCertificate.code"
    "StructuralExhaustion.CT1.TargetCertificateEncoding.Code"
    `StructuralExhaustion.CT1.TargetCertificateEncoding.Code
    "Certificate code"
    r"\mathcal{C}(G)"
    "The proof-carrying target code supplied directly to a local CT1 execution.",
  capabilityConcept "CT1.targetCertificate.accepts"
    "StructuralExhaustion.CT1.TargetCertificateEncoding.Accepts"
    `StructuralExhaustion.CT1.TargetCertificateEncoding.Accepts
    "Certificate acceptance"
    r"\operatorname{Accepts}(G,c)"
    "The proposition certifying that a supplied local code realizes the public target.",
  capabilityConcept "CT1.targetCertificate.encode"
    "StructuralExhaustion.CT1.TargetCertificateEncoding.encode"
    `StructuralExhaustion.CT1.TargetCertificateEncoding.encode
    "Certificate encoder"
    r"T(G)\Rightarrow\exists c,\operatorname{Accepts}(G,c)"
    "A proof that every public target has a corresponding local certificate code.",
  capabilityConcept "CT1.targetCertificate.decode"
    "StructuralExhaustion.CT1.TargetCertificateEncoding.decode"
    `StructuralExhaustion.CT1.TargetCertificateEncoding.decode
    "Certificate decoder"
    r"\operatorname{Accepts}(G,c)\Rightarrow T(G)"
    "A proof that each accepted local certificate establishes the public target."
]

def ct2 : List CapabilityConcept := [
  capabilityConcept "CT2.pieces.piece"
    "StructuralExhaustion.CT2.PieceSystem.Piece"
    `StructuralExhaustion.CT2.PieceSystem.Piece
    "Local piece"
    r"\mathcal{P}(G)"
    "The type of local structures in G that CT2 may delete or replace.",
  capabilityConcept "CT2.pieces.enumeration"
    "StructuralExhaustion.CT2.PieceSystem.pieces"
    `StructuralExhaustion.CT2.PieceSystem.pieces
    "Finite piece enumeration"
    r"\operatorname{pieces}(G)=\mathcal{P}(G)"
    "An exhaustive ordered enumeration of all local pieces in G.",
  capabilityConcept "CT2.pieces.proper"
    "StructuralExhaustion.CT2.PieceSystem.Proper"
    `StructuralExhaustion.CT2.PieceSystem.Proper
    "Proper-piece predicate"
    r"\operatorname{Proper}(p)"
    "The application-defined proposition marking p as a genuine reduction candidate.",
  capabilityConcept "CT2.pieces.admissible"
    "StructuralExhaustion.CT2.PieceSystem.Admissible"
    `StructuralExhaustion.CT2.PieceSystem.Admissible
    "Admissibility predicate"
    r"\operatorname{Admissible}(s,p)"
    "The proposition that piece p may be reduced in the current branch state s.",
  capabilityConcept "CT2.pieces.properDecidable"
    "StructuralExhaustion.CT2.PieceSystem.properDecidable"
    `StructuralExhaustion.CT2.PieceSystem.properDecidable
    "Properness decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Proper}(p)\right)"
    "Executable evidence deciding whether a piece is proper.",
  capabilityConcept "CT2.pieces.admissibleDecidable"
    "StructuralExhaustion.CT2.PieceSystem.admissibleDecidable"
    `StructuralExhaustion.CT2.PieceSystem.admissibleDecidable
    "Admissibility decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Admissible}(s,p)\right)"
    "Executable evidence deciding whether a piece is admissible in a branch.",
  capabilityConcept "CT2.interfaces.interfaceType"
    "StructuralExhaustion.CT2.InterfaceSystem.Interface"
    `StructuralExhaustion.CT2.InterfaceSystem.Interface
    "Boundary interface"
    r"\mathcal{I}"
    "The type of boundary signatures through which pieces interact with their surroundings.",
  capabilityConcept "CT2.interfaces.ofPiece"
    "StructuralExhaustion.CT2.InterfaceSystem.interface"
    `StructuralExhaustion.CT2.InterfaceSystem.interface
    "Piece interface"
    r"\partial p\in\mathcal{I}"
    "Assigns to each local piece its exact boundary interface.",
  capabilityConcept "CT2.contexts.abstractPiece"
    "StructuralExhaustion.CT2.ContextSystem.AbstractPiece"
    `StructuralExhaustion.CT2.ContextSystem.AbstractPiece
    "Abstract piece"
    r"\mathcal{A}(\iota)"
    "The type of replaceable abstract interiors compatible with interface iota.",
  capabilityConcept "CT2.contexts.contextType"
    "StructuralExhaustion.CT2.ContextSystem.Context"
    `StructuralExhaustion.CT2.ContextSystem.Context
    "Outside context"
    r"\mathcal{K}(\iota)"
    "The type of outside environments having boundary interface iota.",
  capabilityConcept "CT2.contexts.enumeration"
    "StructuralExhaustion.CT2.ContextSystem.contexts"
    `StructuralExhaustion.CT2.ContextSystem.contexts
    "Finite context enumeration"
    r"\operatorname{contexts}(\iota)=\mathcal{K}(\iota)"
    "An exhaustive ordered enumeration of the outside contexts for each interface.",
  capabilityConcept "CT2.contexts.glue"
    "StructuralExhaustion.CT2.ContextSystem.glue"
    `StructuralExhaustion.CT2.ContextSystem.glue
    "Gluing operation"
    r"\operatorname{glue}_{\iota}:\mathcal{K}(\iota)\times\mathcal{A}(\iota)\to\mathcal{G}"
    "Reconstructs an ambient object by placing an abstract piece into an outside context.",
  capabilityConcept "CT2.contexts.abstract"
    "StructuralExhaustion.CT2.ContextSystem.abstract"
    `StructuralExhaustion.CT2.ContextSystem.abstract
    "Piece abstraction"
    r"\operatorname{abstract}(p)\in\mathcal{A}(\partial p)"
    "Extracts the abstract interior represented by a concrete piece.",
  capabilityConcept "CT2.contexts.currentContext"
    "StructuralExhaustion.CT2.ContextSystem.currentContext"
    `StructuralExhaustion.CT2.ContextSystem.currentContext
    "Current outside context"
    r"\operatorname{currentContext}(p)\in\mathcal{K}(\partial p)"
    "Extracts the outside environment surrounding the concrete piece in G.",
  capabilityConcept "CT2.contexts.reconstruct"
    "StructuralExhaustion.CT2.ContextSystem.reconstruct"
    `StructuralExhaustion.CT2.ContextSystem.reconstruct
    "Reconstruction law"
    r"\operatorname{glue}(\operatorname{currentContext}(p),\operatorname{abstract}(p))=G"
    "A proof that the context and abstraction recover the original ambient object exactly.",
  capabilityConcept "CT2.observable.baselineDecidable"
    "StructuralExhaustion.CT2.Observable.baselineDecidable"
    `StructuralExhaustion.CT2.Observable.baselineDecidable
    "Baseline decision procedure"
    r"\operatorname{decide}\!\left(B(G)\right)"
    "Executable evidence deciding the problem's baseline property on an ambient object.",
  capabilityConcept "CT2.observable.targetDecidable"
    "StructuralExhaustion.CT2.Observable.targetDecidable"
    `StructuralExhaustion.CT2.Observable.targetDecidable
    "Target decision procedure"
    r"\operatorname{decide}\!\left(T(G)\right)"
    "Executable evidence deciding the target property on an ambient object.",
  capabilityConcept "CT2.reduction.delete"
    "StructuralExhaustion.CT2.ReductionOps.delete"
    `StructuralExhaustion.CT2.ReductionOps.delete
    "Deletion operation"
    r"G\setminus p\prec G"
    "Constructs the certified smaller ambient object obtained by deleting p.",
  capabilityConcept "CT2.replacements.candidate"
    "StructuralExhaustion.CT2.ReplacementSystem.Candidate"
    `StructuralExhaustion.CT2.ReplacementSystem.Candidate
    "Replacement candidate"
    r"\mathcal{R}(p)"
    "The type of candidate replacements available for a concrete piece p.",
  capabilityConcept "CT2.replacements.enumeration"
    "StructuralExhaustion.CT2.ReplacementSystem.candidates"
    `StructuralExhaustion.CT2.ReplacementSystem.candidates
    "Finite replacement enumeration"
    r"\operatorname{candidates}(p)=\mathcal{R}(p)"
    "An exhaustive ordered enumeration of candidate replacements for p.",
  capabilityConcept "CT2.replacements.replacement"
    "StructuralExhaustion.CT2.ReplacementSystem.replacement"
    `StructuralExhaustion.CT2.ReplacementSystem.replacement
    "Replacement interpretation"
    r"\operatorname{replacement}(p,r)\in\mathcal{A}(\partial p)"
    "Interprets candidate r as an abstract piece with the same interface as p.",
  capabilityConcept "CT2.replacements.decreases"
    "StructuralExhaustion.CT2.ReplacementSystem.decreases"
    `StructuralExhaustion.CT2.ReplacementSystem.decreases
    "Replacement decrease proof"
    r"\rho\!\left(\operatorname{glue}(K_p,\operatorname{replacement}(p,r))\right)<\rho(G)"
    "A proof that every enumerated replacement produces a strictly smaller ambient object.",
  capabilityConcept "CT2.deletionClosure.preservesBaseline"
    "StructuralExhaustion.CT2.DeletionClosureRule.preservesBaseline"
    `StructuralExhaustion.CT2.DeletionClosureRule.preservesBaseline
    "Deletion preserves baseline"
    r"B(G)\land\operatorname{Eligible}(s,p)\Rightarrow B(G\setminus p)"
    "The deletion-only profile's proof that an eligible deletion preserves the baseline property.",
  capabilityConcept "CT2.deletionClosure.targetMonotone"
    "StructuralExhaustion.CT2.DeletionClosureRule.targetMonotone"
    `StructuralExhaustion.CT2.DeletionClosureRule.targetMonotone
    "Deletion target monotonicity"
    r"B(G)\land\operatorname{Eligible}(s,p)\land T(G\setminus p)\Rightarrow T(G)"
    "The deletion-only profile's proof that a target in the reduced object lifts to the original object.",
  capabilityConcept "CT2.localDeletion.preservesBaseline"
    "StructuralExhaustion.CT2.LocalDeletionClosureRule.preservesBaseline"
    `StructuralExhaustion.CT2.LocalDeletionClosureRule.preservesBaseline
    "Local deletion preserves baseline"
    r"B(G)\land\operatorname{Eligible}(s,p)\Rightarrow B(G\setminus p)"
    "The local-deletion profile's proof that an eligible deletion preserves the baseline property.",
  capabilityConcept "CT2.localDeletion.targetMonotone"
    "StructuralExhaustion.CT2.LocalDeletionClosureRule.targetMonotone"
    `StructuralExhaustion.CT2.LocalDeletionClosureRule.targetMonotone
    "Local deletion target monotonicity"
    r"B(G)\land\operatorname{Eligible}(s,p)\land T(G\setminus p)\Rightarrow T(G)"
    "The local-deletion profile's proof that a target in the reduced object lifts to the original object.",
  capabilityConcept "CT2.certifiedReduction.reduction"
    "StructuralExhaustion.CT2.CertifiedReductionInput.reduction"
    `StructuralExhaustion.CT2.CertifiedReductionInput.reduction
    "Certified smaller object"
    r"H\prec G"
    "The explicitly supplied local reduction together with its strict rank decrease.",
  capabilityConcept "CT2.certifiedReduction.reducedBaseline"
    "StructuralExhaustion.CT2.CertifiedReductionInput.reducedBaseline"
    `StructuralExhaustion.CT2.CertifiedReductionInput.reducedBaseline
    "Reduced baseline"
    r"B(H)"
    "A proof that the supplied smaller object retains the problem baseline.",
  capabilityConcept "CT2.certifiedReduction.targetMonotone"
    "StructuralExhaustion.CT2.CertifiedReductionInput.targetMonotone"
    `StructuralExhaustion.CT2.CertifiedReductionInput.targetMonotone
    "Certified target transport"
    r"T(H)\Rightarrow T(G)"
    "A proof that every target certificate in the supplied smaller object transports to the source object."
]

def ct3 : List CapabilityConcept := [
  capabilityConcept "CT3.spec.piece" "Spec.Piece"
    `StructuralExhaustion.CT3.Spec.Piece
    "Boundaried piece" r"\mathcal{P}"
    "The type of local pieces whose external responses CT3 compares.",
  capabilityConcept "CT3.spec.context" "Spec.Context"
    `StructuralExhaustion.CT3.Spec.Context
    "Response context" r"\mathcal{K}"
    "The type of outside contexts used as exact response coordinates.",
  capabilityConcept "CT3.spec.candidate" "Spec.Candidate"
    `StructuralExhaustion.CT3.Spec.Candidate
    "Compression candidate" r"\mathcal{C}"
    "The type of proposed representatives that may replace a source piece.",
  capabilityConcept "CT3.spec.row" "Spec.Row"
    `StructuralExhaustion.CT3.Spec.Row
    "Known response row" r"\mathcal{L}"
    "The type of predeclared response rows used to classify a source piece.",
  capabilityConcept "CT3.spec.response" "Spec.response"
    `StructuralExhaustion.CT3.Spec.response
    "Exact response" r"R:\mathcal{P}\times\mathcal{K}\to\{0,1\}"
    "Computes the exact Boolean behavior of a piece in an outside context.",
  capabilityConcept "CT3.spec.candidatePiece" "Spec.candidatePiece"
    `StructuralExhaustion.CT3.Spec.candidatePiece
    "Candidate interpretation" r"\operatorname{piece}:\mathcal{C}\to\mathcal{P}"
    "Interprets a compression candidate as the piece it represents.",
  capabilityConcept "CT3.spec.admissible" "Spec.Admissible"
    `StructuralExhaustion.CT3.Spec.Admissible
    "Candidate admissibility" r"\operatorname{Admissible}(G,p,c)"
    "The proposition that candidate c is allowed to replace source piece p in G.",
  capabilityConcept "CT3.spec.smaller" "Spec.Smaller"
    `StructuralExhaustion.CT3.Spec.Smaller
    "Strictly smaller candidate" r"\operatorname{Smaller}(G,p,c)"
    "The proposition that candidate c gives a genuine size reduction for p in G.",
  capabilityConcept "CT3.spec.rowPiece" "Spec.rowPiece"
    `StructuralExhaustion.CT3.Spec.rowPiece
    "Row representative" r"\operatorname{rowPiece}:\mathcal{L}\to\mathcal{P}"
    "Selects the canonical piece represented by a known response row.",
  capabilityConcept "CT3.spec.rowResponse" "Spec.rowResponse"
    `StructuralExhaustion.CT3.Spec.rowResponse
    "Row response" r"R_{\ell}:\mathcal{K}\to\{0,1\}"
    "Gives the declared exact response vector associated with a known row.",
  capabilityConcept "CT3.capability.contexts" "Capability.contexts"
    `StructuralExhaustion.CT3.Capability.contexts
    "Finite context enumeration" r"\operatorname{contexts}=\mathcal{K}"
    "An exhaustive ordered enumeration of every response coordinate.",
  capabilityConcept "CT3.capability.candidates" "Capability.candidates"
    `StructuralExhaustion.CT3.Capability.candidates
    "Finite candidate enumeration" r"\operatorname{candidates}=\mathcal{C}"
    "An exhaustive ordered enumeration of all compression candidates.",
  capabilityConcept "CT3.capability.rows" "Capability.rows"
    `StructuralExhaustion.CT3.Capability.rows
    "Finite row enumeration" r"\operatorname{rows}=\mathcal{L}"
    "An exhaustive ordered enumeration of all known response rows.",
  capabilityConcept "CT3.capability.admissibleDecidable" "Capability.admissibleDecidable"
    `StructuralExhaustion.CT3.Capability.admissibleDecidable
    "Admissibility decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Admissible}(G,p,c)\right)"
    "Executable evidence deciding whether a candidate is admissible.",
  capabilityConcept "CT3.capability.smallerDecidable" "Capability.smallerDecidable"
    `StructuralExhaustion.CT3.Capability.smallerDecidable
    "Decrease decision procedure"
    r"\operatorname{decide}\!\left(\operatorname{Smaller}(G,p,c)\right)"
    "Executable evidence deciding whether a candidate is strictly smaller.",
  capabilityConcept "CT3.capability.inputSize" "Capability.inputSize"
    `StructuralExhaustion.CT3.Capability.inputSize
    "Input size" r"n(G)\in\mathbb{N}"
    "The application-specific size measure used in CT3's complexity certificate.",
  capabilityConcept "CT3.capability.workCoefficient" "Capability.workCoefficient"
    `StructuralExhaustion.CT3.Capability.workCoefficient
    "Work coefficient" r"c\in\mathbb{N}"
    "The coefficient in the certified polynomial bound on CT3 checks.",
  capabilityConcept "CT3.capability.workDegree" "Capability.workDegree"
    `StructuralExhaustion.CT3.Capability.workDegree
    "Work degree" r"d\in\mathbb{N}"
    "The degree in the certified polynomial bound on CT3 checks.",
  capabilityConcept "CT3.capability.workBound" "Capability.workBound"
    `StructuralExhaustion.CT3.Capability.workBound
    "Polynomial work bound"
    r"\operatorname{checks}\le c\,(n(G)+1)^d"
    "A proof that the full context, candidate, and row schedule satisfies the declared bound.",
  capabilityConcept "CT3.literal.glue"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.glue"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.glue
    "Literal graph gluing" r"X\oplus_TY"
    "The union of the mapped atom-side and outside-context edge sets.",
  capabilityConcept "CT3.literal.contextOwnership"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.Context.noBoundaryEdge"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.Context.noBoundaryEdge
    "Boundary-edge ownership" r"E(Y[T])=\varnothing"
    "The normalized outside context owns no boundary--boundary edge; the atom side owns those edges.",
  capabilityConcept "CT3.literal.reconstruct"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.reconstruct"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.reconstruct
    "Graph reconstruction" r"X\oplus_TY\cong G"
    "A graph isomorphism identifying the literal gluing with the selected ambient graph.",
  capabilityConcept "CT3.literal.connected"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.connected"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.connected
    "Connected atom" r"\operatorname{Connected}(X)"
    "The literal atom-side graph is connected.",
  capabilityConcept "CT3.literal.proper"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.proper"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom.proper
    "Proper atom" r"\rho(X)<\rho(G)"
    "The reconstructed atom is a proper local support of the ambient graph.",
  capabilityConcept "CT3.literal.boundaryDegreeEq"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.boundaryDegree_eq"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.boundaryDegree_eq
    "Boundary-degree equality" r"\mathbf d_\partial(X')=\mathbf d_\partial(X)"
    "The replacement and source lie in the same boundary-degree fibre.",
  capabilityConcept "CT3.literal.obstructionIncluded"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.obstructionIncluded"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.obstructionIncluded
    "Obstruction inclusion" r"\profile_T(X')\subseteq\profile_T(X)"
    "Every replacement target response in an outside context transports to the source; two-way equivalence is not assumed.",
  capabilityConcept "CT3.literal.internalTargetFree"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalTargetFree"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalTargetFree
    "Internal target avoidance" r"\neg\operatorname{Target}(X')"
    "The replacement piece alone contains no selected target cycle.",
  capabilityConcept "CT3.literal.internalBaseline"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalBaseline"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.internalBaseline
    "Replacement internal degree" r"\delta_{\mathrm{int}}(X')\ge d"
    "Every internal replacement vertex meets the minimum-degree threshold.",
  capabilityConcept "CT3.literal.locallySmaller"
    "StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.locallySmaller"
    `StructuralExhaustion.Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.locallySmaller
    "Local lexicographic decrease" r"(|V_{\mathrm{int}}(X')|,|E(X')|)<_{\rm lex}(|V_{\mathrm{int}}(X)|,|E(X)|)"
    "Only the replacement piece is assumed smaller; whole-graph decrease is derived."
]

def ct4 : List CapabilityConcept := [
  capabilityConcept "CT4.spec.demand" "Spec.Demand"
    `StructuralExhaustion.CT4.Spec.Demand
    "Demand" r"\mathcal{D}"
    "The type of obligations that must each be assigned an eligible payer.",
  capabilityConcept "CT4.spec.payer" "Spec.Payer"
    `StructuralExhaustion.CT4.Spec.Payer
    "Payer" r"\mathcal{Q}"
    "The type of resources that may pay for demands.",
  capabilityConcept "CT4.spec.eligible" "Spec.Eligible"
    `StructuralExhaustion.CT4.Spec.Eligible
    "Eligibility relation" r"q\sim_{x}d"
    "The proposition that payer q is allowed to serve demand d in branch context x.",
  capabilityConcept "CT4.spec.demandWeight" "Spec.demandWeight"
    `StructuralExhaustion.CT4.Spec.demandWeight
    "Demand weight" r"w_x:\mathcal{D}\to\mathbb{N}"
    "Assigns the amount charged by each demand in a branch context.",
  capabilityConcept "CT4.spec.capacity" "Spec.capacity"
    `StructuralExhaustion.CT4.Spec.capacity
    "Payer capacity" r"\kappa_x:\mathcal{Q}\to\mathbb{N}"
    "Assigns the maximum permitted load to each payer in a branch context.",
  capabilityConcept "CT4.capability.demands" "Capability.demands"
    `StructuralExhaustion.CT4.Capability.demands
    "Finite demand enumeration" r"\operatorname{demands}=\mathcal{D}"
    "An exhaustive ordered enumeration of all demands.",
  capabilityConcept "CT4.capability.payers" "Capability.payers"
    `StructuralExhaustion.CT4.Capability.payers
    "Finite payer enumeration" r"\operatorname{payers}=\mathcal{Q}"
    "An exhaustive ordered enumeration of all possible payers.",
  capabilityConcept "CT4.capability.eligibleDecidable" "Capability.eligibleDecidable"
    `StructuralExhaustion.CT4.Capability.eligibleDecidable
    "Eligibility decision procedure" r"\operatorname{decide}(q\sim_x d)"
    "Executable evidence deciding whether a payer is eligible for a demand.",
  capabilityConcept "CT4.capability.required" "Capability.required"
    `StructuralExhaustion.CT4.Capability.required
    "Required total" r"R(x)\in\mathbb{N}"
    "The branch-specific aggregate amount against which the computed charge is compared.",
  capabilityConcept "CT4.functional.demand"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.Demand"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.Demand
    "Functional-profile demand" r"\mathcal{D}"
    "The finite demand type in the functional strict-cardinality specialization.",
  capabilityConcept "CT4.functional.payer"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.Payer"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.Payer
    "Functional-profile payer" r"\mathcal{Q}"
    "The finite payer type in the functional strict-cardinality specialization.",
  capabilityConcept "CT4.functional.eligible"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.Eligible"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.Eligible
    "Functional eligibility" r"q\sim_x d"
    "The profile's relation specifying which payer can serve each demand.",
  capabilityConcept "CT4.functional.demands"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.demands"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.demands
    "Functional demand enumeration" r"\operatorname{demands}=\mathcal{D}"
    "An exhaustive ordered enumeration of the profile's demands.",
  capabilityConcept "CT4.functional.payers"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.payers"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.payers
    "Functional payer enumeration" r"\operatorname{payers}=\mathcal{Q}"
    "An exhaustive ordered enumeration of the profile's payers.",
  capabilityConcept "CT4.functional.eligibleDecidable"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.eligibleDecidable"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.eligibleDecidable
    "Functional eligibility decision" r"\operatorname{decide}(q\sim_x d)"
    "Executable evidence deciding the profile's eligibility relation.",
  capabilityConcept "CT4.functional.functional"
    "StructuralExhaustion.CT4.FunctionalCardinalityProfile.functional"
    `StructuralExhaustion.CT4.FunctionalCardinalityProfile.functional
    "Functional payer law"
    r"(q\sim_x d_1\land q\sim_x d_2)\Rightarrow d_1=d_2"
    "A proof that one payer cannot serve two distinct demands, making any total assignment injective."
]

def ct5 : List CapabilityConcept := [
  capabilityConcept "CT5.spec.site" "Spec.Site"
    `StructuralExhaustion.CT5.Spec.Site
    "Local site" r"\mathcal{S}"
    "The type of local positions at which CT5 searches for supporting witnesses.",
  capabilityConcept "CT5.spec.witness" "Spec.Witness"
    `StructuralExhaustion.CT5.Spec.Witness
    "Site witness" r"\mathcal{W}(s)"
    "The dependent type of witnesses available at site s.",
  capabilityConcept "CT5.spec.active" "Spec.Active"
    `StructuralExhaustion.CT5.Spec.Active
    "Activity predicate" r"\operatorname{Active}(x,s)"
    "The proposition that site s is active in branch context x.",
  capabilityConcept "CT5.spec.supports" "Spec.Supports"
    `StructuralExhaustion.CT5.Spec.Supports
    "Support predicate" r"\operatorname{Supports}(x,s,w)"
    "The proposition that witness w supplies valid support at site s.",
  capabilityConcept "CT5.spec.contribution" "Spec.contribution"
    `StructuralExhaustion.CT5.Spec.contribution
    "Witness contribution" r"c_x(s,w)\in\mathbb{N}"
    "Assigns the amount contributed by a supporting witness.",
  capabilityConcept "CT5.capability.sites" "Capability.sites"
    `StructuralExhaustion.CT5.Capability.sites
    "Finite site enumeration" r"\operatorname{sites}=\mathcal{S}"
    "An exhaustive ordered enumeration of all local sites.",
  capabilityConcept "CT5.capability.witnesses" "Capability.witnesses"
    `StructuralExhaustion.CT5.Capability.witnesses
    "Finite witness enumeration" r"\operatorname{witnesses}(s)=\mathcal{W}(s)"
    "An exhaustive ordered enumeration of the witnesses for each site.",
  capabilityConcept "CT5.capability.activeDecidable" "Capability.activeDecidable"
    `StructuralExhaustion.CT5.Capability.activeDecidable
    "Activity decision procedure" r"\operatorname{decide}(\operatorname{Active}(x,s))"
    "Executable evidence deciding whether a site is active.",
  capabilityConcept "CT5.capability.supportsDecidable" "Capability.supportsDecidable"
    `StructuralExhaustion.CT5.Capability.supportsDecidable
    "Support decision procedure" r"\operatorname{decide}(\operatorname{Supports}(x,s,w))"
    "Executable evidence deciding whether a witness supports a site.",
  capabilityConcept "CT5.capability.required" "Capability.required"
    `StructuralExhaustion.CT5.Capability.required
    "Required contribution" r"R(x)\in\mathbb{N}"
    "The total contribution required in the current branch.",
  capabilityConcept "CT5.capability.capacity" "Capability.capacity"
    `StructuralExhaustion.CT5.Capability.capacity
    "Available capacity" r"K(x)\in\mathbb{N}"
    "The total contribution capacity available in the current branch."
]

def ct6 : List CapabilityConcept := [
  capabilityConcept "CT6.spec.index" "Spec.Index"
    `StructuralExhaustion.CT6.Spec.Index
    "Activity index" r"\mathcal{I}"
    "The type of local checks inspected in a fixed order.",
  capabilityConcept "CT6.spec.failureData" "Spec.FailureData"
    `StructuralExhaustion.CT6.Spec.FailureData
    "Failure payload" r"\mathcal{F}"
    "The type of application-specific data extracted from a local failure.",
  capabilityConcept "CT6.spec.failure" "Spec.Failure"
    `StructuralExhaustion.CT6.Spec.Failure
    "Failure predicate" r"\operatorname{Failure}(x,i)"
    "The proposition that local activity fails at index i in branch x.",
  capabilityConcept "CT6.spec.failureDataFunction" "Spec.failureData"
    `StructuralExhaustion.CT6.Spec.failureData
    "Failure-data extractor"
    r"\operatorname{failureData}_x(i):\operatorname{Failure}(x,i)\to\mathcal{F}"
    "Converts proof of a local failure into its typed application-specific payload.",
  capabilityConcept "CT6.spec.contribution" "Spec.contribution"
    `StructuralExhaustion.CT6.Spec.contribution
    "Index contribution" r"c_x:\mathcal{I}\to\mathbb{N}"
    "Assigns the contribution recorded for each nonfailing activity index.",
  capabilityConcept "CT6.capability.failureOrder" "Capability.failureOrder"
    `StructuralExhaustion.CT6.Capability.failureOrder
    "Finite failure order" r"(i_1,\ldots,i_m)"
    "An exhaustive ordered enumeration determining the first-failure search order.",
  capabilityConcept "CT6.capability.failureDecidable" "Capability.failureDecidable"
    `StructuralExhaustion.CT6.Capability.failureDecidable
    "Failure decision procedure" r"\operatorname{decide}(\operatorname{Failure}(x,i))"
    "Executable evidence deciding whether activity fails at an index."
]

def ct7 : List CapabilityConcept := [
  capabilityConcept "CT7.spec.object" "Spec.Object"
    `StructuralExhaustion.CT7.Spec.Object
    "Compared object" r"\mathcal{O}"
    "The type of objects whose context behavior CT7 compares.",
  capabilityConcept "CT7.spec.context" "Spec.Context"
    `StructuralExhaustion.CT7.Spec.Context
    "Realization context" r"\mathcal{K}"
    "The type of finite contexts capable of distinguishing two objects.",
  capabilityConcept "CT7.spec.realizes" "Spec.Realizes"
    `StructuralExhaustion.CT7.Spec.Realizes
    "Realization predicate" r"\operatorname{Realizes}(x,o,k)"
    "The proposition that object o realizes the target behavior in context k.",
  capabilityConcept "CT7.spec.response" "Spec.response"
    `StructuralExhaustion.CT7.Spec.response
    "Declared response" r"R_x:\mathcal{O}\times\mathcal{K}\to\{0,1\}"
    "The Boolean response assigned to an object-context pair.",
  capabilityConcept "CT7.capability.contexts" "Capability.contexts"
    `StructuralExhaustion.CT7.Capability.contexts
    "Finite comparison contexts" r"\mathcal{K}_x(a,b)"
    "An exhaustive ordered context enumeration specialized to the branch and object pair.",
  capabilityConcept "CT7.capability.realizesDecidable" "Capability.realizesDecidable"
    `StructuralExhaustion.CT7.Capability.realizesDecidable
    "Realization decision procedure" r"\operatorname{decide}(\operatorname{Realizes}(x,o,k))"
    "Executable evidence deciding the exact realization predicate."
]

def ct8 : List CapabilityConcept := [
  capabilityConcept "CT8.capability.state" "Capability.State"
    `StructuralExhaustion.CT8.Capability.State
    "Sequence state" r"\mathcal{S}"
    "The type of local states appearing in the finite sequence analyzed by CT8.",
  capabilityConcept "CT8.capability.exactType" "Capability.ExactType"
    `StructuralExhaustion.CT8.Capability.ExactType
    "Exact state type" r"\mathcal{T}"
    "The type of exact classifications used to detect repeated local states.",
  capabilityConcept "CT8.capability.responseContext" "Capability.ResponseContext"
    `StructuralExhaustion.CT8.Capability.ResponseContext
    "Response context" r"\mathcal{K}"
    "The type of external tests used to compare two repeated states.",
  capabilityConcept "CT8.capability.exactTypes" "Capability.exactTypes"
    `StructuralExhaustion.CT8.Capability.exactTypes
    "Finite exact-type enumeration" r"\operatorname{exactTypes}=\mathcal{T}"
    "An exhaustive ordered enumeration of all exact state types.",
  capabilityConcept "CT8.capability.responseContexts" "Capability.responseContexts"
    `StructuralExhaustion.CT8.Capability.responseContexts
    "Finite response contexts" r"\operatorname{responseContexts}=\mathcal{K}"
    "An exhaustive ordered enumeration of all external response tests.",
  capabilityConcept "CT8.capability.exactTypeFunction" "Capability.exactType"
    `StructuralExhaustion.CT8.Capability.exactType
    "Exact-type classifier" r"\tau:\mathcal{S}\to\mathcal{T}"
    "Assigns the exact finite type used to detect repetitions.",
  capabilityConcept "CT8.capability.response" "Capability.response"
    `StructuralExhaustion.CT8.Capability.response
    "State response" r"R:\mathcal{S}\times\mathcal{K}\to\{0,1\}"
    "Computes a state's exact Boolean response in an external context.",
  capabilityConcept "CT8.input.remove" "Input.remove"
    `StructuralExhaustion.CT8.Input.remove
    "Repeated-state removal" r"\operatorname{remove}(s_1,s_2)\prec G"
    "Constructs a certified smaller ambient object from a chosen pair of repeated states."
]

def ct9 : List CapabilityConcept := [
  capabilityConcept "CT9.capability.item" "Capability.Item"
    `StructuralExhaustion.CT9.Capability.Item
    "Active item" r"\mathcal{X}"
    "The type of active items partitioned into label fibres.",
  capabilityConcept "CT9.capability.labelType" "Capability.Label"
    `StructuralExhaustion.CT9.Capability.Label
    "Fibre label" r"\mathcal{L}"
    "The finite type of labels indexing the partition fibres.",
  capabilityConcept "CT9.capability.labels" "Capability.labels"
    `StructuralExhaustion.CT9.Capability.labels
    "Finite label enumeration" r"\operatorname{labels}=\mathcal{L}"
    "An exhaustive ordered enumeration of all fibre labels.",
  capabilityConcept "CT9.capability.labelFunction" "Capability.label"
    `StructuralExhaustion.CT9.Capability.label
    "Item labelling" r"\lambda:\mathcal{X}\to\mathcal{L}"
    "Assigns each active item to exactly one label fibre.",
  capabilityConcept "CT9.capability.capacity" "Capability.capacity"
    `StructuralExhaustion.CT9.Capability.capacity
    "Fibre capacity" r"\kappa:\mathcal{L}\to\mathbb{N}"
    "Assigns the permitted size of each label fibre.",
  capabilityConcept "CT9.parity.item"
    "StructuralExhaustion.CT9.ParityCapacityOneSpec.Item"
    `StructuralExhaustion.CT9.ParityCapacityOneSpec.Item
    "Parity-profile item" r"\mathcal{X}"
    "The item type used by the two-parity, capacity-one specialization.",
  capabilityConcept "CT9.parity.rank"
    "StructuralExhaustion.CT9.ParityCapacityOneSpec.rank"
    `StructuralExhaustion.CT9.ParityCapacityOneSpec.rank
    "Parity rank" r"r:\mathcal{X}\to\mathbb{N}"
    "Assigns each item the natural number whose parity becomes its canonical label."
]

def ct10 : List CapabilityConcept := [
  capabilityConcept "CT10.capability.datum" "Capability.Datum"
    `StructuralExhaustion.CT10.Capability.Datum
    "Local datum" r"\mathcal{D}"
    "The type of local data records classified by CT10.",
  capabilityConcept "CT10.capability.class" "Capability.Class"
    `StructuralExhaustion.CT10.Capability.Class
    "Refinement class" r"\mathcal{C}"
    "The finite type of classes used to partition local data.",
  capabilityConcept "CT10.capability.promotion" "Capability.Promotion"
    `StructuralExhaustion.CT10.Capability.Promotion
    "Promotion payload" r"\mathcal{P}"
    "The type of application-specific residuals produced from a missing class.",
  capabilityConcept "CT10.capability.classes" "Capability.classes"
    `StructuralExhaustion.CT10.Capability.classes
    "Finite class enumeration" r"\operatorname{classes}=\mathcal{C}"
    "An exhaustive ordered enumeration of all refinement classes.",
  capabilityConcept "CT10.capability.classOf" "Capability.classOf"
    `StructuralExhaustion.CT10.Capability.classOf
    "Datum classifier" r"\chi:\mathcal{D}\to\mathcal{C}"
    "Assigns each local datum to its exact refinement class.",
  capabilityConcept "CT10.capability.direct" "Capability.Direct"
    `StructuralExhaustion.CT10.Capability.Direct
    "Directly closing class" r"\operatorname{Direct}(c)"
    "The proposition that class c closes the branch without promotion.",
  capabilityConcept "CT10.capability.directDecidable" "Capability.directDecidable"
    `StructuralExhaustion.CT10.Capability.directDecidable
    "Directness decision procedure" r"\operatorname{decide}(\operatorname{Direct}(c))"
    "Executable evidence deciding whether a refinement class closes directly.",
  capabilityConcept "CT10.capability.promote" "Capability.promote"
    `StructuralExhaustion.CT10.Capability.promote
    "Class promotion" r"\pi:\mathcal{C}\to\mathcal{P}"
    "Converts the first missing nondirect class into its downstream promotion payload."
]

def ct11 : List CapabilityConcept := [
  capabilityConcept "CT11.capability.cell" "Capability.Cell"
    `StructuralExhaustion.CT11.Capability.Cell
    "Budget cell" r"\mathcal{C}"
    "The type of local cells whose integer budgets form the global sum.",
  capabilityConcept "CT11.capability.admissible" "Capability.Admissible"
    `StructuralExhaustion.CT11.Capability.Admissible
    "Cell admissibility" r"\operatorname{Admissible}(x,c)"
    "The proposition that a cell participates validly in the localization argument.",
  capabilityConcept "CT11.capability.admissibleDecidable" "Capability.admissibleDecidable"
    `StructuralExhaustion.CT11.Capability.admissibleDecidable
    "Admissibility decision procedure" r"\operatorname{decide}(\operatorname{Admissible}(x,c))"
    "Executable evidence deciding whether a cell is admissible.",
  capabilityConcept "CT11.capability.localBudget" "Capability.localBudget"
    `StructuralExhaustion.CT11.Capability.localBudget
    "Local integer budget" r"b_x:\mathcal{C}\to\mathbb{Z}"
    "Assigns the signed local contribution whose negative total is localized.",
  capabilityConcept "CT11.negativeBudget.cell"
    "StructuralExhaustion.CT11.NegativeBudgetProfile.Cell"
    `StructuralExhaustion.CT11.NegativeBudgetProfile.Cell
    "Negative-budget cell" r"\mathcal{C}"
    "The cell type for the everywhere-admissible negative-budget specialization.",
  capabilityConcept "CT11.negativeBudget.localBudget"
    "StructuralExhaustion.CT11.NegativeBudgetProfile.localBudget"
    `StructuralExhaustion.CT11.NegativeBudgetProfile.localBudget
    "Negative local budget" r"b_x:\mathcal{C}\to\mathbb{Z}"
    "The profile's signed local budget; a negative total forces a negative cell."
]

def ct12 : List CapabilityConcept := [
  capabilityConcept "CT12.capability.state" "Capability.State"
    `StructuralExhaustion.CT12.Capability.State
    "Load-indexed state" r"\mathcal{S}_n"
    "The type of loop states indexed by their well-founded natural load n.",
  capabilityConcept "CT12.capability.demandResidual" "Capability.DemandResidual"
    `StructuralExhaustion.CT12.Capability.DemandResidual
    "Demand residual" r"\mathcal{D}"
    "The type of semantic demand failures that may terminate peeling.",
  capabilityConcept "CT12.capability.tierResidual" "Capability.TierResidual"
    `StructuralExhaustion.CT12.Capability.TierResidual
    "Tier residual" r"\mathcal{T}"
    "The type of semantic tier failures that may terminate peeling.",
  capabilityConcept "CT12.capability.peeled" "Capability.Peeled"
    `StructuralExhaustion.CT12.Capability.Peeled
    "Peeling result" r"\mathcal{P}(s),\quad s\in\mathcal{S}_{n+1}"
    "The dependent type of exact structural decompositions of a positive-load state.",
  capabilityConcept "CT12.capability.peel" "Capability.peel"
    `StructuralExhaustion.CT12.Capability.peel
    "Peeling operation" r"\operatorname{peel}:\mathcal{S}_{n+1}\to\mathcal{P}(s)"
    "Computes the exact peeled decomposition of a positive-load state.",
  capabilityConcept "CT12.capability.restorations" "Capability.restorations"
    `StructuralExhaustion.CT12.Capability.restorations
    "Restoration options"
    r"\operatorname{restorations}(p)\in\operatorname{NonemptyList}(\mathcal{R}_{n+1})"
    "Produces nonempty finite choices: a strictly smaller continuation or a demand/tier residual.",
  capabilityConcept "CT12.listPeeling.value"
    "StructuralExhaustion.CT12.ListPeeling.Profile.Value"
    `StructuralExhaustion.CT12.ListPeeling.Profile.Value
    "List element" r"V"
    "The sole authored type in the canonical profile that repeatedly removes a list head.",
  capabilityConcept "CT12.disjointPacking.vertices"
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.vertices"
    `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.vertices
    "Host vertices" r"V(G)"
    "The exact finite host-vertex schedule used to bound the selected packing.",
  capabilityConcept "CT12.disjointPacking.finiteItems"
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.finiteItems"
    `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.finiteItems
    "Finite item family" r"|\mathcal I|<\infty"
    "Finiteness used only to prove existence of a maximum disjoint family.",
  capabilityConcept "CT12.disjointPacking.support"
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.support"
    `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.support
    "Item support" r"S(i)\subseteq V(G)"
    "The finite host-vertex support occupied by one packing item.",
  capabilityConcept "CT12.disjointPacking.representative"
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative"
    `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative
    "Support representative" r"r(i)\in V(G)"
    "One host vertex chosen from each support for the linear packing bound.",
  capabilityConcept "CT12.disjointPacking.representativeMem"
    "StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative_mem"
    `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.representative_mem
    "Representative membership" r"r(i)\in S(i)"
    "Proof that every item support is nonempty at its declared representative."
]

def ct13 : List CapabilityConcept := [
  capabilityConcept "CT13.capability.payer"
    "StructuralExhaustion.CT13.Capability.Payer"
    `StructuralExhaustion.CT13.Capability.Payer
    "Tier-one payer" r"\mathcal{P}"
    "The type of candidate payers searched at the first availability tier.",
  capabilityConcept "CT13.capability.payers"
    "StructuralExhaustion.CT13.Capability.payers"
    `StructuralExhaustion.CT13.Capability.payers
    "Finite payer enumeration" r"\operatorname{payers}=\mathcal{P}"
    "An exhaustive ordered enumeration of all tier-one payer candidates.",
  capabilityConcept "CT13.capability.eligible"
    "StructuralExhaustion.CT13.Capability.Eligible"
    `StructuralExhaustion.CT13.Capability.Eligible
    "Tier-one eligibility" r"\operatorname{Eligible}(x,p)"
    "The proposition that payer p is available in the current branch.",
  capabilityConcept "CT13.capability.eligibleDecidable"
    "StructuralExhaustion.CT13.Capability.eligibleDecidable"
    `StructuralExhaustion.CT13.Capability.eligibleDecidable
    "Eligibility decision procedure" r"\operatorname{decide}(\operatorname{Eligible}(x,p))"
    "Executable evidence deciding tier-one payer availability.",
  capabilityConcept "CT13.capability.obstruction"
    "StructuralExhaustion.CT13.Capability.Obstruction"
    `StructuralExhaustion.CT13.Capability.Obstruction
    "Fallback obstruction" r"\mathcal{O}"
    "The type of obstructions considered when no tier-one payer is eligible.",
  capabilityConcept "CT13.capability.obstructions"
    "StructuralExhaustion.CT13.Capability.obstructions"
    `StructuralExhaustion.CT13.Capability.obstructions
    "Finite obstruction enumeration" r"\operatorname{obstructions}=\mathcal{O}"
    "An exhaustive ordered enumeration of fallback obstructions.",
  capabilityConcept "CT13.capability.fallbackDefault"
    "StructuralExhaustion.CT13.Capability.fallbackDefault"
    `StructuralExhaustion.CT13.Capability.fallbackDefault
    "Default obstruction" r"o_0\in\mathcal{O}"
    "A canonical obstruction ensuring that fallback selection is always defined.",
  capabilityConcept "CT13.capability.obstructionCost"
    "StructuralExhaustion.CT13.Capability.obstructionCost"
    `StructuralExhaustion.CT13.Capability.obstructionCost
    "Obstruction cost" r"c_x:\mathcal{O}\to\mathbb{N}"
    "Assigns the cost minimized by the canonical fallback policy.",
  capabilityConcept "CT13.capability.resource"
    "StructuralExhaustion.CT13.Capability.Resource"
    `StructuralExhaustion.CT13.Capability.Resource
    "Resource identity" r"\mathcal{R}"
    "The type used to identify and reconcile resources shared by payers.",
  capabilityConcept "CT13.capability.resourceDecidableEq"
    "StructuralExhaustion.CT13.Capability.resourceDecidableEq"
    `StructuralExhaustion.CT13.Capability.resourceDecidableEq
    "Resource equality decision" r"\operatorname{decide}(r_1=r_2)"
    "Executable equality on resources, used to detect overlap and multiplicity.",
  capabilityConcept "CT13.capability.resourceFunction"
    "StructuralExhaustion.CT13.Capability.resource"
    `StructuralExhaustion.CT13.Capability.resource
    "Payer resource" r"\rho_x:\mathcal{P}\to\mathcal{R}"
    "Assigns to each payer the underlying resource that it consumes.",
  capabilityConcept "CT13.capability.tierTwo"
    "StructuralExhaustion.CT13.Capability.tierTwo"
    `StructuralExhaustion.CT13.Capability.tierTwo
    "Tier-two payers" r"\mathcal{P}_2(x,o)"
    "Returns the ordered payer collection available for a selected fallback obstruction.",
  capabilityConcept "CT13.capability.charge"
    "StructuralExhaustion.CT13.Capability.charge"
    `StructuralExhaustion.CT13.Capability.charge
    "Payer charge" r"q_x:\mathcal{P}\to\mathbb{N}"
    "Assigns the reconciled numerical contribution of each payer.",
  capabilityConcept "CT13.capability.demand"
    "StructuralExhaustion.CT13.Capability.demand"
    `StructuralExhaustion.CT13.Capability.demand
    "Required demand" r"D(x)\in\mathbb{N}"
    "The total branch-specific demand against which reconciled tier-two charge is compared."
]

def ct14 : List CapabilityConcept := [
  capabilityConcept "CT14.capability.member"
    "StructuralExhaustion.CT14.Capability.Member"
    `StructuralExhaustion.CT14.Capability.Member
    "Aggregate member" r"\mathcal{M}"
    "The type of members whose lower masses, capacities, and labels are aggregated.",
  capabilityConcept "CT14.capability.members"
    "StructuralExhaustion.CT14.Capability.members"
    `StructuralExhaustion.CT14.Capability.members
    "Finite member enumeration" r"\operatorname{members}=\mathcal{M}"
    "An exhaustive ordered enumeration of all aggregate members.",
  capabilityConcept "CT14.capability.label"
    "StructuralExhaustion.CT14.Capability.Label"
    `StructuralExhaustion.CT14.Capability.Label
    "Multiplicity label" r"\mathcal{L}"
    "The type of labels whose occurrence multiplicities CT14 records.",
  capabilityConcept "CT14.capability.labelDecidableEq"
    "StructuralExhaustion.CT14.Capability.labelDecidableEq"
    `StructuralExhaustion.CT14.Capability.labelDecidableEq
    "Label equality decision" r"\operatorname{decide}(\ell_1=\ell_2)"
    "Executable equality on labels, used to compute exact multiplicities.",
  capabilityConcept "CT14.capability.memberLowerMass"
    "StructuralExhaustion.CT14.Capability.memberLowerMass"
    `StructuralExhaustion.CT14.Capability.memberLowerMass
    "Member lower mass" r"m_x^-:\mathcal{M}\to\mathbb{N}"
    "Assigns the certified lower mass contributed by each member.",
  capabilityConcept "CT14.capability.memberCapacity"
    "StructuralExhaustion.CT14.Capability.memberCapacity"
    `StructuralExhaustion.CT14.Capability.memberCapacity
    "Optional member capacity" r"\kappa_x:\mathcal{M}\to\mathbb{N}\cup\{\bot\}"
    "Returns a member's upper capacity, or none when no finite capacity is available.",
  capabilityConcept "CT14.capability.memberLabel"
    "StructuralExhaustion.CT14.Capability.memberLabel"
    `StructuralExhaustion.CT14.Capability.memberLabel
    "Optional member label" r"\lambda_x:\mathcal{M}\to\mathcal{L}\cup\{\bot\}"
    "Returns the label counted for a member, or none when the label is missing."
]

def ct15 : List CapabilityConcept := [
  capabilityConcept "CT15.spec.coordinate" "Spec.Coordinate"
    `StructuralExhaustion.CT15.Spec.Coordinate
    "Rank coordinate" r"\mathcal{C}"
    "The finite type of coordinates in the target-relative rank ledger.",
  capabilityConcept "CT15.spec.targetDependent" "Spec.TargetDependent"
    `StructuralExhaustion.CT15.Spec.TargetDependent
    "Target-dependent coordinate" r"\operatorname{TargetDependent}(x,c)"
    "The proposition that coordinate c depends on the target in branch x.",
  capabilityConcept "CT15.spec.charge" "Spec.charge"
    `StructuralExhaustion.CT15.Spec.charge
    "Coordinate charge" r"q_x:\mathcal{C}\to\mathbb{N}"
    "Assigns the ledger charge contributed by each rank coordinate.",
  capabilityConcept "CT15.spec.capacity" "Spec.capacity"
    `StructuralExhaustion.CT15.Spec.capacity
    "Rank capacity" r"K(x)\in\mathbb{N}"
    "The total capacity against which the full-rank charge ledger is compared.",
  capabilityConcept "CT15.capability.coordinates" "Capability.coordinates"
    `StructuralExhaustion.CT15.Capability.coordinates
    "Finite coordinate enumeration" r"\operatorname{coordinates}=\mathcal{C}"
    "An exhaustive ordered enumeration of all rank coordinates.",
  capabilityConcept "CT15.capability.targetDependentDecidable"
    "Capability.targetDependentDecidable"
    `StructuralExhaustion.CT15.Capability.targetDependentDecidable
    "Target-dependence decision"
    r"\operatorname{decide}(\operatorname{TargetDependent}(x,c))"
    "Executable evidence deciding whether a coordinate is target-dependent."
]

def ct16 : List CapabilityConcept := [
  capabilityConcept "CT16.capability.coordinate" "Capability.Coordinate"
    `StructuralExhaustion.CT16.Capability.Coordinate
    "Support coordinate" r"\mathcal{C}"
    "The finite type of coordinates that make up the relevant support.",
  capabilityConcept "CT16.capability.closedCode" "Capability.ClosedCode"
    `StructuralExhaustion.CT16.Capability.ClosedCode
    "Closed-type code" r"\mathcal{Z}"
    "The type of exact codes classifying a whole-support closed object.",
  capabilityConcept "CT16.capability.coordinates" "Capability.coordinates"
    `StructuralExhaustion.CT16.Capability.coordinates
    "Finite support coordinates" r"\operatorname{coordinates}=\mathcal{C}"
    "An exhaustive ordered enumeration of every support coordinate.",
  capabilityConcept "CT16.capability.inSupport" "Capability.InSupport"
    `StructuralExhaustion.CT16.Capability.InSupport
    "Support-membership predicate" r"c\in\operatorname{supp}(G)"
    "The proposition that coordinate c belongs to the support of G.",
  capabilityConcept "CT16.capability.inSupportDecidable" "Capability.inSupportDecidable"
    `StructuralExhaustion.CT16.Capability.inSupportDecidable
    "Support-membership decision" r"\operatorname{decide}(c\in\operatorname{supp}(G))"
    "Executable evidence deciding whether a coordinate lies in the support.",
  capabilityConcept "CT16.capability.closedCodeFunction" "Capability.closedCode"
    `StructuralExhaustion.CT16.Capability.closedCode
    "Computed closed code" r"z:\mathcal{G}\to\mathcal{Z}"
    "Computes the exact closed-type code of an ambient object after whole support is established.",
  capabilityConcept "CT16.capability.targetCode" "Capability.targetCode"
    `StructuralExhaustion.CT16.Capability.targetCode
    "Target closed code" r"z_\star\in\mathcal{Z}"
    "The distinguished closed-type code that certifies the target case.",
  capabilityConcept "CT16.capability.codeDecidableEq" "Capability.codeDecidableEq"
    `StructuralExhaustion.CT16.Capability.codeDecidableEq
    "Code equality decision" r"\operatorname{decide}(z=z_\star)"
    "Executable equality on closed codes, used for the final exact comparison."
]

def ct17 : List CapabilityConcept := [
  capabilityConcept "CT17.spec.target" "Spec.Target"
    `StructuralExhaustion.CT17.Spec.Target
    "Thickening target" r"\mathcal{T}"
    "The finite type of target patterns considered by the thickening search.",
  capabilityConcept "CT17.spec.offset" "Spec.Offset"
    `StructuralExhaustion.CT17.Spec.Offset
    "Target offset" r"\mathcal{O}"
    "The finite type of offsets used to place or compare target patterns.",
  capabilityConcept "CT17.spec.position" "Spec.Position"
    `StructuralExhaustion.CT17.Spec.Position
    "Scale position" r"\mathcal{P}_s"
    "The scale-indexed type of positions examined inside a finite block.",
  capabilityConcept "CT17.spec.value" "Spec.Value"
    `StructuralExhaustion.CT17.Spec.Value
    "Comparison value" r"\mathcal{V}"
    "The type of exact values compared across targets, blocks, and orbits.",
  capabilityConcept "CT17.spec.targetValue" "Spec.targetValue"
    `StructuralExhaustion.CT17.Spec.targetValue
    "Target value" r"v_T:\mathcal{T}\to\mathcal{V}"
    "Assigns the exact comparison value required by each target.",
  capabilityConcept "CT17.spec.blockValue" "Spec.blockValue"
    `StructuralExhaustion.CT17.Spec.blockValue
    "Block value" r"v_B(x,p,o)\in\mathcal{V}"
    "Computes the value observed at a scale-indexed block position and offset.",
  capabilityConcept "CT17.spec.orbitValue" "Spec.orbitValue"
    `StructuralExhaustion.CT17.Spec.orbitValue
    "Orbit value" r"v_O(x,n,o)\in\mathcal{V}"
    "Computes the orbit-side comparison value at scale n and offset o.",
  capabilityConcept "CT17.spec.compatible" "Spec.Compatible"
    `StructuralExhaustion.CT17.Spec.Compatible
    "Target-offset compatibility" r"\operatorname{Compatible}(x,t,o)"
    "The proposition that offset o is admissible for target t in branch x.",
  capabilityConcept "CT17.capability.targets" "Capability.targets"
    `StructuralExhaustion.CT17.Capability.targets
    "Finite target enumeration" r"\operatorname{targets}=\mathcal{T}"
    "An exhaustive ordered enumeration of all thickening targets.",
  capabilityConcept "CT17.capability.offsets" "Capability.offsets"
    `StructuralExhaustion.CT17.Capability.offsets
    "Finite offset enumeration" r"\operatorname{offsets}=\mathcal{O}"
    "An exhaustive ordered enumeration of all target offsets.",
  capabilityConcept "CT17.capability.positions" "Capability.positions"
    `StructuralExhaustion.CT17.Capability.positions
    "Finite scale positions" r"\operatorname{positions}(s)=\mathcal{P}_s"
    "An exhaustive ordered enumeration of the positions available at every scale.",
  capabilityConcept "CT17.capability.compatibleDecidable" "Capability.compatibleDecidable"
    `StructuralExhaustion.CT17.Capability.compatibleDecidable
    "Compatibility decision procedure"
    r"\operatorname{decide}(\operatorname{Compatible}(x,t,o))"
    "Executable evidence deciding whether a target-offset pair is compatible.",
  capabilityConcept "CT17.capability.valueDecidableEq" "Capability.valueDecidableEq"
    `StructuralExhaustion.CT17.Capability.valueDecidableEq
    "Value equality decision" r"\operatorname{decide}(v_1=v_2)"
    "Executable equality on comparison values, used to certify target hits and mismatches.",
  capabilityConcept "CT17.capability.finiteScaleLimit" "Capability.finiteScaleLimit"
    `StructuralExhaustion.CT17.Capability.finiteScaleLimit
    "Finite scale limit" r"s_{\max}\in\mathbb{N}"
    "The declared bound separating exhaustive finite-scale analysis from survivor arithmetic."
]

/-- Semantic requirement metadata for one canonical tactic. -/
def forTactic (tacticId : String) : List CapabilityConcept :=
  match tacticId with
  | "CT1" => ct1
  | "CT2" => ct2
  | "CT3" => ct3
  | "CT4" => ct4
  | "CT5" => ct5
  | "CT6" => ct6
  | "CT7" => ct7
  | "CT8" => ct8
  | "CT9" => ct9
  | "CT10" => ct10
  | "CT11" => ct11
  | "CT12" => ct12
  | "CT13" => ct13
  | "CT14" => ct14
  | "CT15" => ct15
  | "CT16" => ct16
  | "CT17" => ct17
  | _ => []

/-- Readable alias for callers that phrase the lookup as a query. -/
abbrev conceptsFor := forTactic

end StructuralExhaustion.Canonical.CapabilityConcepts
