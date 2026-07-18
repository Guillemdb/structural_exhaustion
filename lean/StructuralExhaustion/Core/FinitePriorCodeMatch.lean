import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.FinitePriorCodeMatch

universe uStage uCode

structure Profile where
  Stage : Type uStage
  Code : Type uCode
  codeDecEq : DecidableEq Code
  before : Stage → List Stage
  code : Stage → Code

namespace Profile

variable (profile : Profile)

def Matches (current prior : profile.Stage) : Prop :=
  profile.code prior = profile.code current

def matchesDecidable (current prior : profile.Stage) :
    Decidable (profile.Matches current prior) :=
  profile.codeDecEq _ _

def scan (current : profile.Stage) :=
  Core.FiniteSearch.onList (profile.before current)
    (profile.Matches current) (profile.matchesDecidable current)

inductive Outcome (current : profile.Stage) where
  | matched
      (prior : profile.Stage)
      (member : prior ∈ profile.before current)
      (same : profile.Matches current prior)
  | absent
      (none : ∀ prior, prior ∈ profile.before current →
        ¬ profile.Matches current prior)

def run (current : profile.Stage) : profile.Outcome current :=
  match profile.scan current with
  | .found prior member same => .matched prior member same
  | .absent absentProof => .absent absentProof

theorem run_total (current : profile.Stage) :
    (∃ prior member same,
      profile.run current = .matched prior member same) ∨
      (∃ none, profile.run current = .absent none) := by
  cases equation : profile.run current with
  | matched prior member same => exact Or.inl ⟨prior, member, same, rfl⟩
  | absent none => exact Or.inr ⟨none, rfl⟩

end Profile

end StructuralExhaustion.Core.FinitePriorCodeMatch
