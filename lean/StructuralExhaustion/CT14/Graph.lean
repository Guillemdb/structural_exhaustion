import StructuralExhaustion.CT14.Types

namespace StructuralExhaustion.CT14.Graph

inductive NodeId where
  | entry | lowerMass | memberScan | upperCapacity | comparison
  | unboundedTerminal | missingLabelTerminal | aggregateTerminal | capacityTerminal
  deriving Repr, DecidableEq

namespace NodeId
def code : NodeId → String
  | .entry => "CT14.entry"
  | .lowerMass => "CT14.compute.lower-mass"
  | .memberScan => "CT14.search.members"
  | .upperCapacity => "CT14.compute.upper-capacity"
  | .comparison => "CT14.decide.comparison"
  | .unboundedTerminal => "CT14.terminal.residual.unbounded-member"
  | .missingLabelTerminal => "CT14.terminal.residual.missing-label"
  | .aggregateTerminal => "CT14.terminal.certificate.aggregate"
  | .capacityTerminal => "CT14.terminal.residual.capacity"
end NodeId

inductive Terminal where | unbounded | missingLabel | aggregate | capacity
  deriving Repr, DecidableEq
namespace Terminal
def nodeId : Terminal → NodeId
  | .unbounded => .unboundedTerminal
  | .missingLabel => .missingLabelTerminal
  | .aggregate => .aggregateTerminal
  | .capacity => .capacityTerminal
end Terminal

inductive Edge {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | begin : Edge C ctx .entry .lowerMass
  | lower (s : LowerMassState C ctx) : Edge C ctx .lowerMass .memberScan
  | unbounded (r : UnboundedMemberResidual C ctx) :
      Edge C ctx .memberScan .unboundedTerminal
  | missingLabel (r : MissingLabelResidual C ctx) :
      Edge C ctx .memberScan .missingLabelTerminal
  | complete (s : MemberScanState C ctx) : Edge C ctx .memberScan .upperCapacity
  | upper (s : LedgerState C ctx) : Edge C ctx .upperCapacity .comparison
  | aggregate (c : AggregateCertificate C ctx) :
      Edge C ctx .comparison .aggregateTerminal
  | capacity (r : CapacityResidual C ctx) :
      Edge C ctx .comparison .capacityTerminal

namespace Edge
def source {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b : NodeId} (_ : Edge C ctx a b) : NodeId := a
end Edge

inductive Path {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : NodeId → NodeId → Type _ where
  | nil (n : NodeId) : Path C ctx n n
  | cons {a b z : NodeId} : Edge C ctx a b → Path C ctx b z → Path C ctx a z
namespace Path
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    {a b : NodeId} : Path C ctx a b → List NodeId
  | .nil n => [n]
  | .cons e rest => e.source :: rest.trace
end Path

def ValidTrace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (xs : List NodeId) : Prop :=
  ∃ t : Terminal, ∃ path : Path C ctx .entry t.nodeId, path.trace = xs

/-- The CT14 graph has a unique node trace to the capacity residual. -/
theorem trace_eq_of_path_to_capacity
    {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (path : Path C ctx .entry .capacityTerminal) :
    path.trace = [.entry, .lowerMass, .memberScan, .upperCapacity,
      .comparison, .capacityTerminal] := by
  cases path with
  | cons first rest =>
      cases first
      cases rest with
      | cons second rest =>
          cases second
          cases rest with
          | cons third rest =>
              cases third with
              | unbounded residual =>
                  cases rest with
                  | cons impossible _tail => cases impossible
              | missingLabel residual =>
                  cases rest with
                  | cons impossible _tail => cases impossible
              | complete scan =>
                  cases rest with
                  | cons fourth rest =>
                      cases fourth
                      cases rest with
                      | cons fifth rest =>
                          cases fifth with
                          | aggregate certificate =>
                              cases rest with
                              | cons impossible _tail => cases impossible
                          | capacity residual =>
                              cases rest with
                              | nil => rfl
                              | cons impossible _tail => cases impossible

end StructuralExhaustion.CT14.Graph
