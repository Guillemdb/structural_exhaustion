import Hypostructure.Core.Problem

/-!
# Domain-independent locality
-/

namespace Hypostructure.Core

universe uAmbient uBranch uWindow uLocal

/-- Nested windows and exact restriction of represented ambient objects. -/
structure Locality (P : Problem.{uAmbient, uBranch}) where
  Window : Type uWindow
  nested : Window -> Window -> Prop
  nestedRefl : forall window, nested window window
  nestedTrans : forall {core work ambient},
    nested core work -> nested work ambient -> nested core ambient
  LocalObject : Window -> Type uLocal
  restrict : P.Ambient -> (window : Window) -> LocalObject window
  restrictNested : forall {core work},
    nested core work -> LocalObject work -> LocalObject core
  restrictNested_eq : forall {core work} (contained : nested core work)
    (object : P.Ambient),
    restrictNested contained (restrict object work) = restrict object core

end Hypostructure.Core
