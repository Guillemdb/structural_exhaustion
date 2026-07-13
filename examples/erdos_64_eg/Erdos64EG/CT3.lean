import Erdos64EG.CT2
import StructuralExhaustion.CT3.TargetCompression

namespace Erdos64EG.Internal

open StructuralExhaustion

universe uVertex uPiece uCompatible uCoordinate uCandidate uRow

/-!
# CT3: boundaried target-response compression

This file specializes the manuscript's boundaried response contract to the
power-of-two-cycle target.  Compatible contexts are classified into certified
finite response coordinates.  The generic CT3 engine compares those local
vectors, searches the finite replacement schedule, validates the table, and
performs row lookup.

Structural admissibility and the manuscript's strict lexicographic decrease
are executable fields of the problem-specific contract.
-/

/-- The Erdős--Gyárfás specialization of the reusable target-compression
contract.  `glue piece context` is the manuscript operation `X ⊕_T Y`;
the remaining fields carry structural admissibility, strict lexicographic
decrease, finite schedules, and primitive deciders. -/
abbrev BoundariedCompressionContract (V : Type uVertex) :=
  CT3.TargetCompressionContract (problem V) (@Target V)

/-- The exact Boolean entry of the manuscript response vector. -/
def targetResponse {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (piece : contract.Piece) (coordinate : contract.Coordinate) : Bool :=
  contract.response piece coordinate

/-- Translate the problem-specific manuscript vocabulary into CT3's
problem-independent specification. -/
def ct3Spec {V : Type uVertex}
    (contract : BoundariedCompressionContract V) : CT3.Spec (problem V) :=
  contract.spec

/-- The finite domains and decision procedures required by the generic CT3
runner are exactly those supplied by the manuscript contract. -/
def ct3Capability {V : Type uVertex}
    (contract : BoundariedCompressionContract V) :
    CT3.Capability (ct3Spec contract) :=
  contract.capability

/-- Materialize a CT3 input without changing the shared branch context. -/
def ct3Input {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) : CT3.Input (ct3Spec contract) :=
  contract.input branch piece

/-- Run the framework on a problem-specific boundaried compression
contract. -/
def runCT3 {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) :=
  contract.run branch piece

/-- A response bit is true exactly when the corresponding glued graph has
the public power-of-two-cycle target. -/
theorem targetResponse_eq_true_iff {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (piece : contract.Piece) (context : contract.CompatibleContext) :
    targetResponse contract piece (contract.classify context) = true ↔
      Target (contract.glue piece context) :=
  contract.response_eq_true_iff piece context

/-- CT3's exact response equality is precisely the manuscript statement that
the two pieces have the same target answer in every declared compatible
context. -/
theorem sameResponse_target_iff {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    {left right : contract.Piece}
    (same : CT3.SameResponse (ct3Spec contract) left right)
    (context : contract.CompatibleContext) :
    Target (contract.glue left context) ↔
      Target (contract.glue right context) :=
  contract.sameResponse_target_iff same context

/-- The generic inclusion theorem gives the one-way replacement implication
used by the proof whenever exact response equality has been certified. -/
theorem sameResponse_targetIncluded {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    {left right : contract.Piece}
    (same : CT3.SameResponse (ct3Spec contract) left right)
    (context : contract.CompatibleContext) :
    Target (contract.glue left context) →
      Target (contract.glue right context) :=
  contract.sameResponse_targetIncluded same context

/-- The complete local CT3 schedule is bounded by the polynomial certificate
carried by the manuscript contract. -/
theorem runCT3_checkLimit {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) :
    (runCT3 contract branch piece).checkLimit ≤ contract.workCoefficient *
      (contract.inputSize branch.G + 1) ^ contract.workDegree :=
  contract.run_checkLimit_polynomial branch piece

/-- Every problem-specific CT3 execution proves the structural claim carried
by the terminal it reaches. -/
theorem runCT3_verified {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) :
    CT3.OutcomeClaim (runCT3 contract branch piece).outcome :=
  contract.run_verified branch piece

/-- Every problem-specific CT3 execution carries a kernel-typed path whose
erased node list is exactly its reported trace. -/
theorem runCT3_traceValid {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) :
    @CT3.Graph.ValidTrace (problem V) (ct3Spec contract)
      (ct3Capability contract) (ct3Input contract branch piece)
      (runCT3 contract branch piece).trace :=
  contract.run_traceValid branch piece

/-- Finite manuscript data determine a verified CT3 result and a valid typed
trace. -/
theorem runCT3_total {V : Type uVertex}
    (contract : BoundariedCompressionContract V)
    (branch : Core.BranchContext (problem V))
    (piece : contract.Piece) :
    ∃ result : CT3.ExecutionResult (ct3Spec contract)
        (ct3Capability contract) (ct3Input contract branch piece),
      CT3.OutcomeClaim result.outcome ∧
        @CT3.Graph.ValidTrace (problem V) (ct3Spec contract)
          (ct3Capability contract) (ct3Input contract branch piece)
          result.trace :=
  contract.run_total branch piece

end Erdos64EG.Internal
