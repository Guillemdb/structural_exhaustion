import StructuralExhaustion.CT2.Observation
import StructuralExhaustion.CT2.ReductionOps
import StructuralExhaustion.CT2.ReplacementSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

/-! One reusable CT2 capability kit.  It contains mathematical vocabulary,
finite enumerators, and primitive operations, never a node implementation. -/

structure Capability (P : Core.Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) where
  pieces : PieceSystem.{uAmbient, uBranch, uPiece} P
  interfaces : InterfaceSystem.{uAmbient, uBranch, uPiece, uInterface} pieces
  contexts : ContextSystem.{uAmbient, uBranch, uPiece, uInterface,
    uAbstract, uContext} interfaces
  observable : Observable P Target
  reductions : ReductionOps pieces
  replacements : ReplacementSystem.{uAmbient, uBranch, uPiece, uInterface,
    uAbstract, uContext, uCandidate} contexts

/-- CT2 is invoked only after generic piece discovery has constructed a seed. -/
structure Input
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P Target)
    (context : Core.MinimalCounterexampleContext P Target) where
  seed : Seed capability.pieces context

namespace Capability

/-- Generic capability discovery; disabled results carry exact impossibility. -/
def discover
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P Target)
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.Routing.Discovery (Input capability ctx) :=
  match capability.pieces.discover ctx with
  | .enabled seed => .enabled ⟨seed⟩
  | .disabled reject => .disabled fun input => reject input.seed

end Capability

end StructuralExhaustion.CT2
