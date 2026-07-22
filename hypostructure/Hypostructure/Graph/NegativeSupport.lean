import Hypostructure.Core.Residual.Query
import Hypostructure.Core.SupportSplit
import Hypostructure.Graph.Finite
import Hypostructure.Graph.SupportComponents

/-!
# Parameterized negative graph supports

This module owns the graph meaning of a finite connected support carrying a
negative signed charge.  The charge, connectivity proof, baseline, scale, and
threshold are contract data.  Graph derives only the ambient degree split;
Core and Routes own branch execution and ledger transport.
-/

namespace Hypostructure.Graph.NegativeSupport

open Hypostructure.Core.Residual

universe uPrevious u

variable {Previous : Sort uPrevious}

structure Support (object : FiniteObject.{u}) where
  source : Hypostructure.Core.SupportSplit.Source object.Vertex
  connected : Hypostructure.Graph.SupportComponents.Connected.ConnectedOn
    object source.core

namespace Support

variable {object : FiniteObject.{u}}

abbrev core (support : Support object) : Finset object.Vertex :=
  support.source.core

abbrev charge (support : Support object) : object.Vertex -> Int :=
  support.source.charge

theorem negative (support : Support object) :
    (support.source.cells.values.map support.charge).sum < 0 :=
  support.source.negative

def chargeTotal (support : Support object) : Int :=
  ∑ vertex ∈ support.core, support.charge vertex

@[simp] theorem chargeTotal_eq (support : Support object) :
    support.chargeTotal = ∑ vertex ∈ support.core, support.charge vertex :=
  rfl

def highCenters (support : Support object) (threshold : Nat) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact support.core.filter fun vertex => threshold ≤ object.degree vertex

structure High (support : Support object) (threshold : Nat) where
  center : object.Vertex
  center_mem : center ∈ support.core
  threshold_le : threshold ≤ object.degree center

structure Low (support : Support object) (threshold : Nat) where
  noHigh : support.highCenters threshold = ∅

def HasHigh (support : Support object) (threshold : Nat) : Prop :=
  (support.highCenters threshold).Nonempty

def HasNoHigh (support : Support object) (threshold : Nat) : Prop :=
  support.highCenters threshold = ∅

instance hasHighDecidable (support : Support object) (threshold : Nat) :
    Decidable (support.HasHigh threshold) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  unfold HasHigh highCenters
  infer_instance

instance hasNoHighDecidable (support : Support object) (threshold : Nat) :
    Decidable (support.HasNoHigh threshold) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  unfold HasNoHigh highCenters
  infer_instance

noncomputable def highWitnessOfHasHigh
    (support : Support object) (threshold : Nat)
    (high : support.HasHigh threshold) : support.High threshold := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let center := high.choose
  have member := high.choose_spec
  have filtered := Finset.mem_filter.mp member
  exact ⟨center, filtered.1, filtered.2⟩

theorem noHigh_of_not_hasHigh
    (support : Support object) (threshold : Nat)
    (notHigh : ¬ support.HasHigh threshold) :
    support.HasNoHigh threshold := by
  unfold HasHigh HasNoHigh at *
  exact Finset.not_nonempty_iff_eq_empty.mp notHigh

theorem high_or_noHigh (support : Support object) (threshold : Nat) :
    support.HasHigh threshold ∨ support.HasNoHigh threshold := by
  rcases Finset.eq_empty_or_nonempty (support.highCenters threshold) with
    empty | nonempty
  · exact Or.inr empty
  · exact Or.inl nonempty

theorem ambientDegree_eq_of_noHigh
    (support : Support object) (baseline threshold : Nat)
    (threshold_eq : threshold = baseline + 1)
    (minimumDegreeBaseline : baseline ≤ object.minDegree)
    (noHigh : support.HasNoHigh threshold) :
    ∀ vertex ∈ support.core, object.degree vertex = baseline := by
  intro vertex member
  have lower : baseline ≤ object.degree vertex :=
    minimumDegreeBaseline.trans (object.minDegree_le_degree vertex)
  have notHigh : ¬ threshold ≤ object.degree vertex := by
    intro high
    have highMember : vertex ∈ support.highCenters threshold := by
      letI : DecidableEq object.Vertex := object.vertices.decEq
      exact Finset.mem_filter.mpr ⟨member, high⟩
    rw [noHigh] at highMember
    simp at highMember
  subst threshold
  omega

end Support

/-! ## Typed predecessor-query projections -/

namespace QuerySurface

abbrev ObjectQuery :=
  Query Previous (fun _previous => FiniteObject.{u})

abbrev SupportQuery (object : ObjectQuery) :=
  Query Previous (fun previous => Support (object.read previous))

def highCentersQuery (object : ObjectQuery)
    (support : SupportQuery object)
    (threshold : Query Previous (fun _previous => Nat)) :
    Query Previous (fun previous =>
      Finset (object.read previous).Vertex) :=
  support.map fun previous value => value.highCenters (threshold.read previous)

noncomputable def hasHighDecisionQuery (object : ObjectQuery)
    (support : SupportQuery object)
    (threshold : Query Previous (fun _previous => Nat)) :
    Query Previous (fun previous =>
      Decidable ((support.read previous).HasHigh (threshold.read previous))) :=
  support.dependentMap fun previous value =>
    Support.hasHighDecidable value (threshold.read previous)

noncomputable def hasNoHighDecisionQuery (object : ObjectQuery)
    (support : SupportQuery object)
    (threshold : Query Previous (fun _previous => Nat)) :
    Query Previous (fun previous =>
      Decidable ((support.read previous).HasNoHigh (threshold.read previous))) :=
  support.dependentMap fun previous value =>
    Support.hasNoHighDecidable value (threshold.read previous)

end QuerySurface

end Hypostructure.Graph.NegativeSupport
