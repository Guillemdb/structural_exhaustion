import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Context
import Hypostructure.Core.Provision
import Hypostructure.Core.Routing
import Hypostructure.Core.SemanticEquivalence

/-!
# Generic closure mechanisms

Core recognizes exactly five ways to close a branch.  Every constructor below
contains the mathematical evidence that performs the closure; identifiers and
names are metadata and never close a branch by themselves.
-/

namespace Hypostructure.Core.Closure

universe uAmbient uBranch uMeasure uResource

/-- The exhaustive framework classification of closure mechanisms. -/
inductive Mechanism where
  | direct
  | strictProgress
  | resourceContradiction
  | importedContract
  | acyclicReduction
  deriving Repr, DecidableEq

/-- Direct closure is either a typed certificate or an actual contradiction. -/
inductive DirectEvidence (Conclusion : Prop) where
  | certificate (proof : Conclusion)
  | contradiction (impossible : False)

namespace DirectEvidence

def proof {Conclusion : Prop} : DirectEvidence Conclusion -> Conclusion
  | .certificate conclusion => conclusion
  | .contradiction impossible => impossible.elim

end DirectEvidence

/-- Exact evidence for the strict-progress/minimality closure pattern. -/
structure StrictProgressEvidence
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    (context : MinimalCounterexampleContext P Target progress) where
  candidate : AvoidingContext P Target
  smaller : progress.Smaller candidate.G context.G

namespace StrictProgressEvidence

def contradiction
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {context : MinimalCounterexampleContext P Target progress}
    (evidence : StrictProgressEvidence context) : False :=
  context.contradiction_of_smaller evidence.candidate evidence.smaller

end StrictProgressEvidence

/-- Exact lower/actual/upper resource transcript whose endpoints are
incompatible. -/
structure ResourceEvidence
    (budget : ResourceBudget.{uResource}) where
  lower : budget.Resource
  actual : budget.Resource
  upper : budget.Resource
  lower_le_actual : budget.le lower actual
  actual_le_upper : budget.le actual upper
  endpoints_impossible : Not (budget.le lower upper)

namespace ResourceEvidence

def contradiction {budget : ResourceBudget.{uResource}}
    (evidence : ResourceEvidence budget) : False :=
  evidence.endpoints_impossible
    (budget.leTrans evidence.lower_le_actual evidence.actual_le_upper)

end ResourceEvidence

/-- A named imported theorem closes only through its exact typed statement and
proof.  The declaration reference alone has no eliminator. -/
structure ExactImportedContract (Conclusion : Prop) where
  source : DeclarationRef
  Statement : Prop
  theoremProof : Statement
  conclude : Statement -> Conclusion

namespace ExactImportedContract

def proof {Conclusion : Prop}
    (contract : ExactImportedContract Conclusion) : Conclusion :=
  contract.conclude contract.theoremProof

end ExactImportedContract

/-- Reduction to an already closed obstruction.  Semantic coordinate
agreement, transport of closedness, and strict routing-rank descent are all
mandatory fields. -/
structure AcyclicReduction
    {P : Problem.{uAmbient, uBranch}}
    (semantics : SemanticEquivalence P)
    (ClosedObstruction : P.Ambient -> Prop)
    (source destination : P.Ambient) where
  destinationClosed : ClosedObstruction destination
  coordinateCompatible : semantics.equivalent source destination
  transportObstruction : semantics.equivalent source destination ->
    ClosedObstruction destination -> ClosedObstruction source
  sourceRank : Nat
  destinationRank : Nat
  rankDecreases : Routing.StrictRankDecrease sourceRank destinationRank

namespace AcyclicReduction

def close
    {P : Problem.{uAmbient, uBranch}}
    {semantics : SemanticEquivalence P}
    {ClosedObstruction : P.Ambient -> Prop}
    {source destination : P.Ambient}
    (reduction : AcyclicReduction semantics ClosedObstruction source destination) :
    ClosedObstruction source :=
  reduction.transportObstruction reduction.coordinateCompatible
    reduction.destinationClosed

end AcyclicReduction

/-- A terminal proof tagged by the mechanism that Core actually checked.  The
constructor is private; the five functions below are the complete public
construction surface. -/
structure Result (Conclusion : Prop) where
  private mk ::
  mechanism : Mechanism
  proof : Conclusion

namespace Result

def direct {Conclusion : Prop} (evidence : DirectEvidence Conclusion) :
    Result Conclusion :=
  .mk .direct evidence.proof

def strictProgress {Conclusion : Prop}
    {P : Problem.{uAmbient, uBranch}}
    {Target : P.Ambient -> Prop}
    {progress : Progress.{uAmbient, uBranch, uMeasure} P}
    {context : MinimalCounterexampleContext P Target progress}
    (evidence : StrictProgressEvidence context) : Result Conclusion :=
  .mk .strictProgress evidence.contradiction.elim

def resourceContradiction {Conclusion : Prop}
    {budget : ResourceBudget.{uResource}}
    (evidence : ResourceEvidence budget) : Result Conclusion :=
  .mk .resourceContradiction evidence.contradiction.elim

def importedContract {Conclusion : Prop}
    (contract : ExactImportedContract Conclusion) : Result Conclusion :=
  .mk .importedContract contract.proof

def acyclicReduction
    {P : Problem.{uAmbient, uBranch}}
    {semantics : SemanticEquivalence P}
    {ClosedObstruction : P.Ambient -> Prop}
    {source destination : P.Ambient}
    (reduction : AcyclicReduction semantics ClosedObstruction source destination) :
    Result (ClosedObstruction source) :=
  .mk .acyclicReduction reduction.close

end Result

end Hypostructure.Core.Closure
