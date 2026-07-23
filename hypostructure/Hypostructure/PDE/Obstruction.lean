import Hypostructure.PDE.Model

/-!
# PDE obstruction profiles

Graph has generic induced-obstruction targets.  PDE uses the same separation:
the profile names a represented analytic pattern, while CT1 and later routes
decide realization from residual-owned candidates.  No family of points,
scales, or functions is enumerated here.
-/

namespace Hypostructure.PDE.Obstruction

universe u uPattern

structure Profile (M : PDE.LocalModel.{u}) where
  Pattern : Type uPattern
  realizes : Pattern -> M.problem.Ambient -> Prop
  realizesDecidable : (pattern : Pattern) ->
    (object : M.problem.Ambient) -> Decidable (realizes pattern object)

def Has {M : PDE.LocalModel.{u}}
    (profile : Profile M) (object : M.problem.Ambient) : Prop :=
  Exists fun pattern => profile.realizes pattern object

def Free {M : PDE.LocalModel.{u}}
    (profile : Profile M) (object : M.problem.Ambient) : Prop :=
  Not (Has profile object)

theorem free_iff {M : PDE.LocalModel.{u}}
    (profile : Profile M) (object : M.problem.Ambient) :
    Free profile object ↔
      forall pattern, Not (profile.realizes pattern object) := by
  constructor
  · intro free pattern realizes
    exact free ⟨pattern, realizes⟩
  · intro all has
    rcases has with ⟨pattern, realizes⟩
    exact all pattern realizes

end Hypostructure.PDE.Obstruction
