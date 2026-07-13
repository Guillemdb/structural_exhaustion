import StructuralExhaustion.CT3.Search

namespace StructuralExhaustion.CT3.Graph

open StructuralExhaustion

universe uAmbient uBranch uPiece uContext uCandidate uRow

/-- Exact nodes of the automation-first CT3 reference machine. -/
inductive NodeId where
  | entry
  | vectorComputation
  | compressionSearch
  | tableValidation
  | rowLookup
  | compressionTerminal
  | distinguishingTerminal
  | knownRowTerminal
  | novelRowTerminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT3.entry"
  | .vectorComputation => "CT3.compute.exact-vector"
  | .compressionSearch => "CT3.search.compression"
  | .tableValidation => "CT3.validate.table"
  | .rowLookup => "CT3.lookup.exact-row"
  | .compressionTerminal => "CT3.terminal.compression"
  | .distinguishingTerminal => "CT3.terminal.distinguishing-context"
  | .knownRowTerminal => "CT3.terminal.known-row"
  | .novelRowTerminal => "CT3.terminal.novel-row"

end NodeId

/-- Structural CT3 terminals.  Destination selection is deliberately absent. -/
inductive Terminal where
  | compression
  | distinguishing
  | knownRow
  | novelRow
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .compression => .compressionTerminal
  | .distinguishing => .distinguishingTerminal
  | .knownRow => .knownRowTerminal
  | .novelRow => .novelRowTerminal

end Terminal

/-- Every transition carries precisely the evidence produced by its source. -/
inductive Edge {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT3.Spec P)
    (C : CT3.Capability S) (input : CT3.Input S) :
    NodeId → NodeId → Type _ where
  | beginVector : Edge S C input .entry .vectorComputation
  | vectorReady (vector : CT3.ExactVectorState S input) :
      Edge S C input .vectorComputation .compressionSearch
  | compressionFound {vector : CT3.ExactVectorState S input}
      (certificate : CT3.CompressionCertificate S C input vector) :
      Edge S C input .compressionSearch .compressionTerminal
  | compressionAbsent {vector : CT3.ExactVectorState S input}
      (state : CT3.UncompressibleExternalType S C input vector) :
      Edge S C input .compressionSearch .tableValidation
  | tableDefect
      (residual : CT3.DistinguishingContextResidual S C input) :
      Edge S C input .tableValidation .distinguishingTerminal
  | tableExact (table : CT3.ExactTableState S C) :
      Edge S C input .tableValidation .rowLookup
  | rowKnown {table : CT3.ExactTableState S C}
      (certificate : CT3.KnownRowCertificate S C input table) :
      Edge S C input .rowLookup .knownRowTerminal
  | rowNovel {table : CT3.ExactTableState S C}
      (residual : CT3.NovelExternalTypeResidual S C input table) :
      Edge S C input .rowLookup .novelRowTerminal

namespace Edge

def source {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT3.Spec P}
    {C : CT3.Capability S} {input : CT3.Input S}
    {first second : NodeId} (_edge : Edge S C input first second) : NodeId :=
  first

def target {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT3.Spec P}
    {C : CT3.Capability S} {input : CT3.Input S}
    {first second : NodeId} (_edge : Edge S C input first second) : NodeId :=
  second

end Edge

/-- Dependent CT3 path; an ill-composed trace is unrepresentable. -/
inductive Path {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT3.Spec P)
    (C : CT3.Capability S) (input : CT3.Input S) :
    NodeId → NodeId → Type _ where
  | nil (node : NodeId) : Path S C input node node
  | cons {first second last : NodeId} :
      Edge S C input first second →
      Path S C input second last →
      Path S C input first last

namespace Path

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT3.Spec P}
    {C : CT3.Capability S} {input : CT3.Input S}
    {first last : NodeId} : Path S C input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT3.Spec P}
    {C : CT3.Capability S} {input : CT3.Input S}
    (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path S C input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT3.Graph
