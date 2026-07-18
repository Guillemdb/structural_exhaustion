import StructuralExhaustion.Core.FiniteFirstFailure
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FiniteFirstFailureLedger

open StructuralExhaustion

universe uCorridor uStage uF1 uF2 uF3 uF4 uGerm

/-!
# Exact ledgers for finite first-failure runs

This is the aggregate bookkeeping layer for `FiniteFirstFailure`.  It maps
the runner over one explicit, ordered source list and partitions the resulting
dependent entries into the four first-event constructors and the exhaustive
quiet/F5 constructor.  No outcome is accepted from a caller.
-/

variable {Corridor : Type uCorridor} {Stage : Type uStage}

abbrev Profile := Core.FiniteFirstFailure.Profile Corridor Stage

inductive Tag
  | f1
  | f2
  | f3
  | f4
  | f5
  deriving DecidableEq

structure Entry
    (profile : Profile (Corridor := Corridor) (Stage := Stage)) where
  source : Corridor
  result : profile.Result source
  resultExact : result = profile.run source

namespace Entry

variable {profile : Profile (Corridor := Corridor) (Stage := Stage)}

def tag (entry : Entry profile) : Tag :=
  match entry.result with
  | .first _ (.f1 _ _) => .f1
  | .first _ (.f2 _ _ _) => .f2
  | .first _ (.f3 _ _ _ _) => .f3
  | .first _ (.f4 _ _ _ _ _) => .f4
  | .germ _ _ => .f5

/-- Every entry retains the literal source on which its stored runner result
was computed. -/
theorem result_provenance (entry : Entry profile) :
    entry.result = profile.run entry.source :=
  entry.resultExact

end Entry

variable (profile : Profile (Corridor := Corridor) (Stage := Stage))

/-- Execute the first-failure runner once on every source, in source order. -/
noncomputable def run (sources : List Corridor) : List (Entry profile) :=
  sources.map fun source => ⟨source, profile.run source, rfl⟩

theorem run_length (sources : List Corridor) :
    (run profile sources).length = sources.length := by
  simp [run]

theorem run_sources (sources : List Corridor) :
    (run profile sources).map Entry.source = sources := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      change source :: (run profile rest).map Entry.source = source :: rest
      rw [ih]

/-- Duplicate-free source schedules remain duplicate-free after execution;
in particular, no selected incidence is silently duplicated by the ledger. -/
theorem run_sources_nodup {sources : List Corridor} (nodup : sources.Nodup) :
    ((run profile sources).map Entry.source).Nodup := by
  rw [run_sources]
  exact nodup

noncomputable def withTag (sources : List Corridor) (tag : Tag) :
    List (Entry profile) :=
  (run profile sources).filter fun entry => entry.tag = tag

private theorem fiveTagPartitionLength (entries : List (Entry profile)) :
    (entries.filter fun entry => entry.tag = Tag.f1).length +
      (entries.filter fun entry => entry.tag = Tag.f2).length +
      (entries.filter fun entry => entry.tag = Tag.f3).length +
      (entries.filter fun entry => entry.tag = Tag.f4).length +
      (entries.filter fun entry => entry.tag = Tag.f5).length =
      entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases tagEquation : entry.tag <;> simp [tagEquation] <;> omega

/-- Exact five-way accounting.  This is a partition of the executed ledger,
not merely an assertion that five predicates cover the source type. -/
theorem partition (sources : List Corridor) :
    (withTag profile sources .f1).length +
      (withTag profile sources .f2).length +
      (withTag profile sources .f3).length +
      (withTag profile sources .f4).length +
      (withTag profile sources .f5).length = sources.length := by
  rw [withTag, withTag, withTag, withTag, withTag,
    fiveTagPartitionLength, run_length]

/-- The visible work is exactly the sum of the explicit local stage-list
lengths attached to the supplied sources. -/
def checks (sources : List Corridor) : Nat :=
  (sources.map profile.checks).sum

theorem checks_append (left right : List Corridor) :
    checks profile (left ++ right) = checks profile left + checks profile right := by
  simp [checks]

end StructuralExhaustion.Core.FiniteFirstFailureLedger
