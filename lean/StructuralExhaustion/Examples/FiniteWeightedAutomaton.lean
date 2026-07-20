import StructuralExhaustion.Core.FiniteWeightedAutomaton

namespace StructuralExhaustion.Examples.FiniteWeightedAutomaton

open Core

/-!
A theorem-independent fixture: binary words with no consecutive selected
positions.  It exercises rejection, exact weight coefficients, semantic
correctness, and product convolution without any graph-specific data.
-/

def noConsecutive : Core.FiniteWeightedAutomaton.Machine Bool Bool where
  symbols := Core.Enumeration.bool
  step previous selected :=
    if previous && selected then none else some selected
  weight selected := if selected then 1 else 0

theorem noConsecutive_length_three_histogram :
    noConsecutive.histogram 3 false 3 = [1, 3, 1, 0] := by
  decide

theorem noConsecutive_length_three_semantic_counts (weight : Nat) :
    (noConsecutive.words 3 false weight).length =
      noConsecutive.count 3 false weight :=
  noConsecutive.words_length_eq_count 3 false weight

theorem noConsecutive_length_three_words_nodup (weight : Nat) :
    (noConsecutive.words 3 false weight).Nodup :=
  noConsecutive.words_nodup 3 false weight

theorem noConsecutive_weight_one_carrier_count :
    (noConsecutive.acceptedWords 3 false 1).card = 3 := by
  rw [noConsecutive.acceptedWords_card_eq_count]
  decide

theorem noConsecutive_identity_transport :
    (noConsecutive.acceptedWords 3 false 1).card =
      noConsecutive.count 3 false 1 := by
  apply noConsecutive.carrier_card_eq_count_of_equiv
  exact Equiv.refl _

theorem noConsecutive_two_by_one_product_weight_two :
    Core.FiniteWeightedAutomaton.convolution
      (noConsecutive.count 2 false)
      (noConsecutive.count 1 false) 2 = 2 := by
  decide

theorem noConsecutive_two_by_one_product_semantics :
    (Core.FiniteWeightedAutomaton.gradedProductWords noConsecutive
      noConsecutive 2 false 1 false 2).length = 2 := by
  rw [Core.FiniteWeightedAutomaton.gradedProductWords_length_eq_convolution]
  exact noConsecutive_two_by_one_product_weight_two

#print axioms noConsecutive_length_three_histogram
#print axioms noConsecutive_length_three_semantic_counts
#print axioms noConsecutive_length_three_words_nodup
#print axioms noConsecutive_weight_one_carrier_count
#print axioms noConsecutive_identity_transport
#print axioms noConsecutive_two_by_one_product_weight_two
#print axioms noConsecutive_two_by_one_product_semantics

end StructuralExhaustion.Examples.FiniteWeightedAutomaton
