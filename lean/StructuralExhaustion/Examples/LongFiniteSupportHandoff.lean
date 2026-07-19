import StructuralExhaustion.Routes.LongFiniteSupportHandoff

namespace StructuralExhaustion.Examples.LongFiniteSupportHandoff

open StructuralExhaustion

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem :=
  ⟨(), trivial, ()⟩

def source : Routes.LongFiniteSupportHandoff.Source context where
  supportLength := 5
  scale := 2
  exceeds := by decide

def residual : Routes.LongFiniteSupportHandoff.Residual context :=
  Routes.LongFiniteSupportHandoff.handoff source

example : residual.source = source := rfl

example : residual.source.scale < residual.source.supportLength := by
  exact residual.source.exceeds

example : (Routes.LongFiniteSupportHandoff.positions source).card = 5 := by
  native_decide

example : (Routes.LongFiniteSupportHandoff.prefixPositions source).card = 3 := by
  native_decide

example (position : Routes.LongFiniteSupportHandoff.PrefixPosition source) :
    (Routes.LongFiniteSupportHandoff.prefixEmbedding source position).1 =
      position.1 :=
  rfl

example (position : Routes.LongFiniteSupportHandoff.PrefixPosition source) :
    (∃ index embeddingExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition source position =
        .base index embeddingExact) ∨
    (∃ overflowExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition source position =
        .overflow overflowExact) :=
  Routes.LongFiniteSupportHandoff.classifyPrefixPosition_exhaustive source position

example (position : Routes.LongFiniteSupportHandoff.PrefixPosition source) :
    (∃ overflowExact,
      Routes.LongFiniteSupportHandoff.classifyPrefixPosition source position =
        .overflow overflowExact) ↔
      position = Routes.LongFiniteSupportHandoff.overflow source :=
  Routes.LongFiniteSupportHandoff.classifyPrefixPosition_overflow_iff source position

example :
    (Routes.LongFiniteSupportHandoff.overflowImage source).1 = source.scale :=
  rfl

example (position : Routes.LongFiniteSupportHandoff.Position source) :
    (∃ index embeddingExact,
      Routes.LongFiniteSupportHandoff.classifyPosition source position =
        .inPrefix index embeddingExact) ∨
    (∃ lowerBound,
      Routes.LongFiniteSupportHandoff.classifyPosition source position =
        .afterPrefix lowerBound) :=
  Routes.LongFiniteSupportHandoff.classifyPosition_exhaustive source position

example : Routes.LongFiniteSupportHandoff.handoffId =
    "finite-long-support->typed-scale-handoff" :=
  rfl

end StructuralExhaustion.Examples.LongFiniteSupportHandoff
