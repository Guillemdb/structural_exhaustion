import StructuralExhaustion.Core.FiniteExactStateCorridor

namespace StructuralExhaustion.Graph.WalkPrefixBoundedExchange

open StructuralExhaustion

universe uVertex uStage uCode

/-!
# Bounded supports between repeated prefix states

The graph-independent finite-state runner returns occurrence indices.  This
module turns those exact indices into the corresponding contiguous support of
one already supplied path list.  It performs no path search.
-/

variable {Vertex : Type uVertex}

noncomputable def supportBetween [DecidableEq Vertex]
    (pathSupport : List Vertex) (firstIndex secondIndex : Nat) : Finset Vertex :=
  ((pathSupport.drop firstIndex).take
    (secondIndex - firstIndex + 1)).toFinset

theorem supportBetween_card_le_span [DecidableEq Vertex]
    (pathSupport : List Vertex) (firstIndex secondIndex : Nat) :
    (supportBetween pathSupport firstIndex secondIndex).card ≤
      secondIndex - firstIndex + 1 := by
  unfold supportBetween
  calc
    ((pathSupport.drop firstIndex).take
        (secondIndex - firstIndex + 1)).toFinset.card
        ≤ ((pathSupport.drop firstIndex).take
          (secondIndex - firstIndex + 1)).length :=
            List.toFinset_card_le _
    _ ≤ secondIndex - firstIndex + 1 := List.length_take_le _ _

variable {Stage : Type uStage} {Code : Type uCode}
variable {profile : Core.FiniteExactStateCorridor.Profile Stage Code}

noncomputable def repeatedSupport [DecidableEq Vertex]
    (pathSupport : List Vertex) (repetition : profile.Repeated) : Finset Vertex :=
  supportBetween pathSupport repetition.firstIndex repetition.secondIndex

/-- The repeat support contains at most `Q + 1` path vertices.  The later
`M_cold = Q_cold + 30` allowance may add the two window interfaces and
boundary-stub decorations separately. -/
theorem repeatedSupport_card_le_stateBound_add_one [DecidableEq Vertex]
    (pathSupport : List Vertex) (repetition : profile.Repeated) :
    (repeatedSupport pathSupport repetition).card ≤ profile.stateBound + 1 := by
  calc
    (repeatedSupport pathSupport repetition).card
        ≤ repetition.secondIndex - repetition.firstIndex + 1 :=
          supportBetween_card_le_span _ _ _
    _ ≤ profile.stateBound + 1 := by
      have := repetition.span_le_bound
      omega

end StructuralExhaustion.Graph.WalkPrefixBoundedExchange
