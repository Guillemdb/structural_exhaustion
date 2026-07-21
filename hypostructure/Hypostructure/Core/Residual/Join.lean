import Hypostructure.Core.Residual.Query

/-!
# Typed residual-ledger joins

A join retains every complete incoming ledger.  Its specification states the
typed compatibility relation and proves that compatible inputs carry the same
residual.  Binary joins compose because a join result is itself a residual
stage, giving finite multi-predecessor joins without arity-specific tuples.
-/

namespace Hypostructure.Core.Residual.Join

universe uResidual uLeft uRight uLeftResult uRightResult

/-- The exact compatibility contract for two incoming ledger stages. -/
structure Spec (Residual : Type uResidual)
    (Left : Sort uLeft) (Right : Sort uRight)
    [HasResidual Left Residual] [HasResidual Right Residual] where
  Compatible : Left -> Right -> Prop
  residual_eq : {left : Left} -> {right : Right} ->
    Compatible left right -> residualOf left = residualOf right

namespace Spec

/-- The canonical join specification when compatibility is literal residual
equality. -/
def sameResidual (Residual : Type uResidual)
    (Left : Sort uLeft) (Right : Sort uRight)
    [HasResidual Left Residual] [HasResidual Right Residual] :
    Spec Residual Left Right where
  Compatible left right := residualOf left = residualOf right
  residual_eq compatible := compatible

end Spec

/-- A typed join of two exact predecessor stages. -/
structure Result {Residual : Type uResidual}
    {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    (spec : Spec Residual Left Right) where
  private mk ::
  left : Left
  right : Right
  compatible : spec.Compatible left right

/-- Execute a typed join from its two literal predecessors and one
compatibility certificate. -/
def execute {Residual : Type uResidual}
    {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    (spec : Spec Residual Left Right) (left : Left) (right : Right)
    (compatible : spec.Compatible left right) :
    Result spec :=
  .mk left right compatible

instance {Residual : Type uResidual}
    {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right} :
    HasResidual (Result spec) Residual where
  residual joined := residualOf joined.left

@[simp] theorem execute_left
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    (spec : Spec Residual Left Right) (left : Left) (right : Right)
    (compatible : spec.Compatible left right) :
    (execute spec left right compatible).left = left :=
  rfl

@[simp] theorem execute_right
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    (spec : Spec Residual Left Right) (left : Left) (right : Right)
    (compatible : spec.Compatible left right) :
    (execute spec left right compatible).right = right :=
  rfl

@[simp] theorem execute_compatible
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    (spec : Spec Residual Left Right) (left : Left) (right : Right)
    (compatible : spec.Compatible left right) :
    (execute spec left right compatible).compatible = compatible :=
  rfl

/-- The exact residual equality certified by a join. -/
theorem Result.residual_eq
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right} (joined : Result spec) :
    residualOf joined.left = residualOf joined.right :=
  spec.residual_eq joined.compatible

@[simp] theorem Result.residual_eq_left
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right} (joined : Result spec) :
    residualOf joined = residualOf joined.left :=
  rfl

/-- Lift any typed query from the complete left predecessor through a join. -/
def leftQuery
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right}
    {Output : Left -> Sort uLeftResult} (query : Query Left Output) :
    Query (Result spec) (fun joined => Output joined.left) :=
  query.comap fun (joined : Result spec) => joined.left

/-- Lift any typed query from the complete right predecessor through a join. -/
def rightQuery
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right}
    {Output : Right -> Sort uRightResult} (query : Query Right Output) :
    Query (Result spec) (fun joined => Output joined.right) :=
  query.comap fun (joined : Result spec) => joined.right

/-- Joining preserves every query from the left predecessor. -/
@[simp] theorem read_leftQuery
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right}
    {Output : Left -> Sort uLeftResult} (query : Query Left Output)
    (joined : Result spec) :
    (leftQuery query).read joined = query.read joined.left :=
  rfl

/-- Joining preserves every query from the right predecessor. -/
@[simp] theorem read_rightQuery
    {Residual : Type uResidual} {Left : Sort uLeft} {Right : Sort uRight}
    [HasResidual Left Residual] [HasResidual Right Residual]
    {spec : Spec Residual Left Right}
    {Output : Right -> Sort uRightResult} (query : Query Right Output)
    (joined : Result spec) :
    (rightQuery query).read joined = query.read joined.right :=
  rfl

end Hypostructure.Core.Residual.Join
