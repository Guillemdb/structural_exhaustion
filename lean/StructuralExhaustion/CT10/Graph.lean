import StructuralExhaustion.CT10.Search

namespace StructuralExhaustion.CT10.Graph

universe uAmbient uBranch uDatum uClass uPromotion

inductive NodeId where
  | entry | table | direct | missing | promotion
  | directTerminal | promotedTerminal | exhaustiveTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT10.entry"
  | .table => "CT10.compute.classTable"
  | .direct => "CT10.search.direct"
  | .missing => "CT10.search.firstMissing"
  | .promotion => "CT10.compute.promotion"
  | .directTerminal => "CT10.terminal.residual.direct"
  | .promotedTerminal => "CT10.terminal.residual.promoted"
  | .exhaustiveTerminal => "CT10.terminal.certificate.exhaustive"
end NodeId

inductive Terminal where | direct | promoted | exhaustive deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .direct => .directTerminal
  | .promoted => .promotedTerminal
  | .exhaustive => .exhaustiveTerminal
end Terminal

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
variable (input : Input capability)

inductive Edge : NodeId → NodeId → Type _ where
  | begin : Edge .entry .table
  | tableBuilt : Edge .table .direct
  | directFound (r : DirectResidual capability) : Edge .direct .directTerminal
  | directAbsent (s : DirectAbsent capability) : Edge .direct .missing
  | missingFound (r : PromotedResidual capability input) : Edge .missing .promotion
  | promoted (r : PromotedResidual capability input) : Edge .promotion .promotedTerminal
  | exhaustive (c : ExhaustiveCertificate capability input) : Edge .missing .exhaustiveTerminal

namespace Edge
def source {a b} (_ : Edge capability input a b) := a
end Edge

inductive Path : NodeId → NodeId → Type _ where
  | nil (n) : Path n n
  | cons {a b c} : Edge capability input a b → Path b c → Path a c
namespace Path
def trace {a b} : Path capability input a b → List NodeId
  | .nil n => [n]
  | .cons e p => e.source :: p.trace
end Path

def ValidTrace (nodes : List NodeId) : Prop := ∃ terminal : Terminal,
  ∃ path : Path capability input .entry terminal.nodeId, path.trace = nodes

/-- The CT10 graph has a unique node trace from entry to the exhaustive
terminal; proof payloads on its edges do not affect that trace. -/
theorem trace_eq_of_path_to_exhaustive
    (path : Path capability input .entry .exhaustiveTerminal) :
    path.trace =
      [.entry, .table, .direct, .missing, .exhaustiveTerminal] := by
  cases path with
  | cons first rest =>
      cases first with
      | begin =>
          cases rest with
          | cons second rest =>
              cases second with
              | tableBuilt =>
                  cases rest with
                  | cons third rest =>
                      cases third with
                      | directFound residual =>
                          cases rest with
                          | cons impossible tail => cases impossible
                      | directAbsent directAbsent =>
                          cases rest with
                          | cons fourth rest =>
                              cases fourth with
                              | missingFound residual =>
                                  cases rest with
                                  | cons promoted rest =>
                                      cases promoted with
                                      | promoted residual =>
                                          cases rest with
                                          | cons impossible tail =>
                                              cases impossible
                              | exhaustive certificate =>
                                  cases rest with
                                  | nil => rfl
                                  | cons impossible tail => cases impossible

end StructuralExhaustion.CT10.Graph
