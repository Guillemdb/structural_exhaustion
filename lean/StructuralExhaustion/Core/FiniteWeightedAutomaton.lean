import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Core.FiniteWeightedAutomaton

universe uState uSymbol

/-!
# Symbolic weighted finite-state counting

The executable recurrence below remembers only the current finite state.  A
separate exact word language supplies its semantics.  Correctness is proved
once by induction, so applications evaluate the recurrence rather than a
power-sized word universe.
-/

/-- A deterministic local automaton.  `none` rejects one extension and the
symbol weight records the coefficient of the resulting word. -/
structure Machine (State : Type uState) (Symbol : Type uSymbol) where
  symbols : FinEnum Symbol
  step : State → Symbol → Option State
  weight : Symbol → Nat

namespace Machine

variable {State : Type uState} {Symbol : Type uSymbol}

/-- Exact accepted words, represented only for the semantic correctness
theorem.  Clients compute with `count`, not with this list. -/
def words (machine : Machine State Symbol) : Nat → State → Nat → List (List Symbol)
  | 0, _state, total => if total = 0 then [[]] else []
  | length + 1, state, total =>
      machine.symbols.orderedValues.flatMap fun symbol =>
        match machine.step state symbol with
        | none => []
        | some next =>
            if machine.weight symbol ≤ total then
              (machine.words length next
                (total - machine.weight symbol)).map (symbol :: ·)
            else []

/-- State-based dynamic-programming recurrence. -/
def count (machine : Machine State Symbol) : Nat → State → Nat → Nat
  | 0, _state, total => if total = 0 then 1 else 0
  | length + 1, state, total =>
      (machine.symbols.orderedValues.map fun symbol =>
        match machine.step state symbol with
        | none => 0
        | some next =>
            if machine.weight symbol ≤ total then
              machine.count length next (total - machine.weight symbol)
            else 0).sum

/-- The state recurrence is the exact cardinality of the accepted word
language. -/
theorem words_length_eq_count (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) :
    (machine.words length state total).length =
      machine.count length state total := by
  induction length generalizing state total with
  | zero =>
      by_cases exactWeight : total = 0 <;> simp [words, count, exactWeight]
  | succ length ih =>
      rw [words, count, List.length_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro symbol _member
      cases transition : machine.step state symbol with
      | none => simp
      | some next =>
          simp only
          split
          · simp [ih]
          · simp

/-- Determinism and the duplicate-free alphabet make the generated accepted
word language duplicate-free.  Different outer fibres have different first
symbols; within one fibre, cons is injective. -/
theorem words_nodup (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) :
    (machine.words length state total).Nodup := by
  induction length generalizing state total with
  | zero =>
      by_cases exactWeight : total = 0 <;> simp [words, exactWeight]
  | succ length ih =>
      rw [words, List.nodup_flatMap]
      constructor
      · intro symbol _symbolMem
        cases transition : machine.step state symbol with
        | none => simp
        | some next =>
            by_cases fits : machine.weight symbol ≤ total
            · simp only [fits, if_true]
              exact (ih next (total - machine.weight symbol)).map (by
                intro left right equality
                exact (List.cons.inj equality).2)
            · simp [fits]
      · apply machine.symbols.nodup_orderedValues.imp_of_mem
        intro left right _leftMem _rightMem different
        change List.Disjoint
          (match machine.step state left with
            | none => []
            | some next =>
                if machine.weight left ≤ total then
                  (machine.words length next
                    (total - machine.weight left)).map (left :: ·)
                else [])
          (match machine.step state right with
            | none => []
            | some next =>
                if machine.weight right ≤ total then
                  (machine.words length next
                    (total - machine.weight right)).map (right :: ·)
                else [])
        rw [List.disjoint_left]
        intro word leftWord rightWord
        have blockHead : ∀ symbol, word ∈
              (match machine.step state symbol with
              | none => []
              | some next =>
                  if machine.weight symbol ≤ total then
                    (machine.words length next
                      (total - machine.weight symbol)).map (symbol :: ·)
                  else []) →
              word.head? = some symbol := by
          intro symbol membership
          cases transition : machine.step state symbol with
          | none => simp [transition] at membership
          | some next =>
              by_cases fits : machine.weight symbol ≤ total
              · simp only [transition, fits, if_true] at membership
                obtain ⟨tail, _tailMem, rfl⟩ := List.mem_map.mp membership
                simp
              · simp [transition, fits] at membership
        have leftHead := blockHead left leftWord
        have rightHead := blockHead right rightWord
        rw [leftHead] at rightHead
        exact different (Option.some.inj rightHead)

/-- Direct recursive semantics, useful when connecting a concrete bounded
gap predicate to the generic machine. -/
def Accepts (machine : Machine State Symbol) :
    State → List Symbol → Nat → Prop
  | _state, [], total => total = 0
  | state, symbol :: tail, total =>
      ∃ next,
        machine.step state symbol = some next ∧
        machine.weight symbol ≤ total ∧
        machine.Accepts next tail (total - machine.weight symbol)

/-- The generated language contains exactly the words recognized by the
transition semantics, with the requested length and weight. -/
theorem mem_words_iff (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) (word : List Symbol) :
    word ∈ machine.words length state total ↔
      word.length = length ∧ machine.Accepts state word total := by
  induction length generalizing state total word with
  | zero =>
      cases word with
      | nil =>
          by_cases exactWeight : total = 0 <;>
            simp [words, Accepts, exactWeight]
      | cons symbol tail => simp [words]
  | succ length ih =>
      cases word with
      | nil =>
          constructor
          · intro membership
            simp only [words, List.mem_flatMap] at membership
            rcases membership with ⟨symbol, _symbolMem, membership⟩
            cases transition : machine.step state symbol with
            | none => simp [transition] at membership
            | some next =>
                by_cases fits : machine.weight symbol ≤ total <;>
                  simp [transition, fits] at membership
          · intro impossible
            simp at impossible
      | cons head tail =>
          simp only [words, Accepts, List.length_cons, Nat.succ.injEq,
            List.mem_flatMap]
          constructor
          · rintro ⟨symbol, _symbolMem, membership⟩
            cases transition : machine.step state symbol with
            | none => simp [transition] at membership
            | some next =>
                by_cases fits : machine.weight symbol ≤ total
                · simp only [transition, fits, if_true] at membership
                  obtain ⟨candidateTail, candidateMem, equality⟩ :=
                    List.mem_map.mp membership
                  have heads : symbol = head := by
                    exact List.cons.inj equality |>.1
                  have tails : candidateTail = tail := by
                    exact List.cons.inj equality |>.2
                  subst symbol
                  subst candidateTail
                  have exactTail :=
                    (ih next (total - machine.weight head) tail).1 candidateMem
                  exact ⟨exactTail.1, next, transition, fits, exactTail.2⟩
                · simp [transition, fits] at membership
          · rintro ⟨tailLength, next, transition, fits, accepted⟩
            refine ⟨head, machine.symbols.mem_orderedValues head, ?_⟩
            simp only [transition, fits, if_true]
            apply List.mem_map.mpr
            exact ⟨tail,
              (ih next (total - machine.weight head) tail).2
                ⟨tailLength, accepted⟩,
              rfl⟩

/-- Exact finite enumeration of the semantic accepted-word carrier. -/
@[implicit_reducible]
def acceptedWords (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) :
    FinEnum {word // word ∈ machine.words length state total} := by
  letI : DecidableEq Symbol := machine.symbols.decEq
  exact FinEnum.ofNodupList
    (machine.words length state total).attach (by simp)
    (machine.words_nodup length state total).attach

/-- The accepted-word subtype has exactly the dynamic-programming count. -/
theorem acceptedWords_card_eq_count (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) :
    (machine.acceptedWords length state total).card =
      machine.count length state total := by
  letI : DecidableEq Symbol := machine.symbols.decEq
  rw [acceptedWords]
  change (machine.words length state total).attach.length = _
  rw [List.length_attach]
  exact machine.words_length_eq_count length state total

/-- Cardinality transport for any concrete carrier proved equivalent to the
accepted local language.  This is the bridge used by fixed-length vectors,
functions, bit words, and graph attachment labels. -/
theorem carrier_card_eq_count_of_equiv
    {Carrier : Type*} (machine : Machine State Symbol)
    (carrier : FinEnum Carrier)
    (length : Nat) (state : State) (total : Nat)
    (equivalence : Carrier ≃
      {word // word ∈ machine.words length state total}) :
    carrier.card = machine.count length state total := by
  letI : Fintype Carrier := @FinEnum.instFintype Carrier carrier
  letI : FinEnum {word // word ∈ machine.words length state total} :=
    machine.acceptedWords length state total
  rw [FinEnum.card_eq_fintypeCard]
  rw [Fintype.card_congr equivalence]
  rw [← FinEnum.card_eq_fintypeCard]
  exact machine.acceptedWords_card_eq_count length state total

/-- One recurrence step, exposed without unfolding implementation details. -/
theorem count_succ (machine : Machine State Symbol)
    (length : Nat) (state : State) (total : Nat) :
    machine.count (length + 1) state total =
      (machine.symbols.orderedValues.map fun symbol =>
        match machine.step state symbol with
        | none => 0
        | some next =>
            if machine.weight symbol ≤ total then
              machine.count length next (total - machine.weight symbol)
            else 0).sum :=
  rfl

/-- Coefficients `0,…,maximumWeight` of the recognized language. -/
def histogram (machine : Machine State Symbol)
    (length : Nat) (state : State) (maximumWeight : Nat) : List Nat :=
  (List.range (maximumWeight + 1)).map (machine.count length state)

end Machine

/-! ## Graded products -/

/-- Coefficient convolution for two finite weighted languages. -/
def convolution (left right : Nat → Nat) (total : Nat) : Nat :=
  ((List.range (total + 1)).map fun leftWeight =>
    left leftWeight * right (total - leftWeight)).sum

/-- The semantic paired language, partitioned by the left weight. -/
def gradedProductWords
    {LeftState : Type*} {RightState : Type*}
    {LeftSymbol : Type*} {RightSymbol : Type*}
    (left : Machine LeftState LeftSymbol)
    (right : Machine RightState RightSymbol)
    (leftLength : Nat) (leftStart : LeftState)
    (rightLength : Nat) (rightStart : RightState)
    (total : Nat) : List (List LeftSymbol × List RightSymbol) :=
  (List.range (total + 1)).flatMap fun leftWeight =>
    (left.words leftLength leftStart leftWeight).flatMap fun leftWord =>
      (right.words rightLength rightStart (total - leftWeight)).map
        fun rightWord => (leftWord, rightWord)

/-- Product languages are counted by coefficient convolution. -/
theorem gradedProductWords_length_eq_convolution
    {LeftState : Type*} {RightState : Type*}
    {LeftSymbol : Type*} {RightSymbol : Type*}
    (left : Machine LeftState LeftSymbol)
    (right : Machine RightState RightSymbol)
    (leftLength : Nat) (leftStart : LeftState)
    (rightLength : Nat) (rightStart : RightState)
    (total : Nat) :
    (gradedProductWords left right leftLength leftStart
      rightLength rightStart total).length =
      convolution (left.count leftLength leftStart)
        (right.count rightLength rightStart) total := by
  simp only [gradedProductWords, List.length_flatMap, List.length_map,
    right.words_length_eq_count, convolution]
  apply congrArg List.sum
  apply List.map_congr_left
  intro leftWeight _member
  simp [left.words_length_eq_count]

end StructuralExhaustion.Core.FiniteWeightedAutomaton
