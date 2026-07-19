import StructuralExhaustion.CT3.Graph
import StructuralExhaustion.CT3.Nodes
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT3

universe uAmbient uBranch uPiece uContext uCandidate uRow

/-- Semantic terminal evidence indexed by the exact terminal reached. -/
inductive RawOutcome {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) :
    Graph.Terminal → Type _ where
  | compression {vector : ExactVectorState S input}
      (certificate : CompressionCertificate S C input vector) :
      RawOutcome S C input .compression
  | distinguishing
      (residual : DistinguishingContextResidual S C input) :
      RawOutcome S C input .distinguishing
  | knownRow {table : ExactTableState S C}
      (certificate : KnownRowCertificate S C input table) :
      RawOutcome S C input .knownRow
  | novelRow {table : ExactTableState S C}
      (residual : NovelExternalTypeResidual S C input table) :
      RawOutcome S C input .novelRow

/-- A result contains a kernel-typed path and evidence indexed by its final
node. -/
structure ExecutionResult {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) :
    Type _ where
  terminal : Graph.Terminal
  path : Graph.Path S C input .entry terminal.nodeId
  outcome : RawOutcome S C input terminal

namespace ExecutionResult

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S}
    (result : ExecutionResult S C input) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

/-- Execute all CT3 decisions from mathematical capability data alone. -/
def runReference {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) : ExecutionResult S C input :=
  let _entry := Nodes.Entry.run input
  let vector := Nodes.Vector.run S input
  match Nodes.Compression.run S C input vector with
  | .compressed certificate => {
      terminal := .compression
      path := .cons .beginVector
        (.cons (.vectorReady vector)
          (.cons (.compressionFound certificate)
            (.nil .compressionTerminal)))
      outcome := .compression certificate
    }
  | .uncompressible uncompressible =>
      match Nodes.TableValidation.run S C uncompressible with
      | .defect residual => {
          terminal := .distinguishing
          path := .cons .beginVector
            (.cons (.vectorReady vector)
              (.cons (.compressionAbsent uncompressible)
                (.cons (.tableDefect residual)
                  (.nil .distinguishingTerminal))))
          outcome := .distinguishing residual
        }
      | .exact table =>
          match Nodes.Lookup.run S C input table with
          | .known certificate => {
              terminal := .knownRow
              path := .cons .beginVector
                (.cons (.vectorReady vector)
                  (.cons (.compressionAbsent uncompressible)
                    (.cons (.tableExact table)
                      (.cons (.rowKnown certificate)
                        (.nil .knownRowTerminal)))))
              outcome := .knownRow certificate
            }
          | .novel residual => {
              terminal := .novelRow
              path := .cons .beginVector
                (.cons (.vectorReady vector)
                  (.cons (.compressionAbsent uncompressible)
                    (.cons (.tableExact table)
                      (.cons (.rowNovel residual)
                        (.nil .novelRowTerminal)))))
              outcome := .novelRow residual
            }

/-- Public CT3 execution preserves the typed path and terminal-indexed
evidence.  No outcome-erasing compatibility facade is exposed. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P)
    (C : Capability S) (input : Input S) : ExecutionResult S C input :=
  runReference S C input

/-- Structural fact established by terminal evidence. -/
def OutcomeClaim {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec P}
    {C : Capability S} {input : Input S} {terminal : Graph.Terminal} :
    RawOutcome S C input terminal → Prop
  | .compression certificate =>
      Compresses S input certificate.candidate
  | .distinguishing residual =>
      S.response (S.rowPiece residual.row) residual.context ≠
        S.rowResponse residual.row residual.context
  | .knownRow certificate =>
      RowMatches S input certificate.row
  | .novelRow residual =>
      ∀ row, ¬ RowMatches S input row

namespace Capability

/-- Canonical executable CT3 entry.  The transition supplies one piece at the
literal inherited branch context; the framework constructs the indexed CT3
input and executes the public reference runner. -/
def executableInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uAmbient, uBranch, uPiece, uContext, uCandidate, uRow} P}
    (capability : Capability S) :
    Core.Routing.ExecutableInterface .ct3 where
  Context := Core.BranchContext P
  Trigger := Trigger S
  Result := fun context trigger =>
    ExecutionResult S capability ⟨context, trigger.piece⟩
  execute := fun context trigger =>
    run S capability ⟨context, trigger.piece⟩

end Capability

end StructuralExhaustion.CT3
