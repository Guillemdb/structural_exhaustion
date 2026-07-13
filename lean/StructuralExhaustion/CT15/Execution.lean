import StructuralExhaustion.CT15.Graph

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uCoordinate} P)
variable (capability : Capability S) (input : Input P)

inductive RawOutcome : Graph.Terminal → Type _ where
  | rankDrop {rank : RankState S capability input}
      (residual : RankDropResidual S capability input rank) :
      RawOutcome .rankDrop
  | c4 {rank : RankState S capability input}
      {full : FullRankState S capability input rank}
      {ledger : LedgerState S capability input full}
      (certificate : C4Certificate S capability input ledger) :
      RawOutcome .c4
  | fullRankLedger {rank : RankState S capability input}
      {full : FullRankState S capability input rank}
      {ledger : LedgerState S capability input full}
      (residual : FullRankLedgerResidual S capability input ledger) :
      RawOutcome .fullRankLedger

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability input .entry terminal.nodeId
  outcome : RawOutcome S capability input terminal

namespace ExecutionResult

def trace (result : ExecutionResult S capability input) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

/-- Pure exhaustive reference interpreter. -/
def runReference : ExecutionResult S capability input :=
  let rank := computeRank S capability input
  match splitRank S capability input rank with
  | .dropped residual => {
      terminal := .rankDrop
      path := .cons .beginRank
        (.cons (.rankComputed rank)
          (.cons (.rankDropped residual) (.nil .rankDropTerminal)))
      outcome := .rankDrop residual
    }
  | .full full =>
      let ledger := buildLedger S capability input full
      match compareLedger S capability input ledger with
      | .closes certificate => {
          terminal := .c4
          path := .cons .beginRank
            (.cons (.rankComputed rank)
              (.cons (.rankFull full)
                (.cons (.ledgerComputed ledger)
                  (.cons (.capacityExceeded certificate)
                    (.nil .c4Terminal)))))
          outcome := .c4 certificate
        }
      | .residual residual => {
          terminal := .fullRankLedger
          path := .cons .beginRank
            (.cons (.rankComputed rank)
              (.cons (.rankFull full)
                (.cons (.ledgerComputed ledger)
                  (.cons (.capacityAvailable residual)
                    (.nil .fullRankLedgerTerminal)))))
          outcome := .fullRankLedger residual
        }

def run : ExecutionResult S capability input :=
  runReference S capability input

end StructuralExhaustion.CT15
