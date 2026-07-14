import StructuralExhaustion.CT14.Execution

namespace StructuralExhaustion.CT14

def RawOutcome.Valid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {terminal} :
    RawOutcome C ctx terminal → Prop
  | .unbounded residual => C.memberCapacity ctx residual.member = none
  | .missingLabel residual => C.memberLabel ctx residual.member = none
  | .aggregate certificate => certificate.upper < certificate.lower
  | .capacity residual => residual.lower ≤ residual.upper

theorem RawOutcome.verified {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} {terminal}
    (outcome : RawOutcome C ctx terminal) : outcome.Valid := by
  cases outcome with
  | unbounded residual => exact residual.missing
  | missingLabel residual => exact residual.missing
  | aggregate certificate => exact certificate.exceeds
  | capacity residual => exact residual.within

theorem ExecutionResult.traceValid {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (result : ExecutionResult C ctx) :
    @Graph.ValidTrace P C ctx result.trace :=
  ⟨result.terminal, result.path, rfl⟩

/-- Extract the actual capacity residual from an execution proved to reach
that terminal.  Refinement routes consume this object rather than rebuilding
the computed lower/upper ledger. -/
def ExecutionResult.capacityResidual {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (result : ExecutionResult C ctx)
    (terminal : result.terminal = .capacity) : CapacityResidual C ctx := by
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | unbounded residual => cases terminal
      | missingLabel residual => cases terminal
      | aggregate certificate => cases terminal
      | capacity residual => exact residual

theorem run_verified {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    (run C ctx input).outcome.Valid :=
  (run C ctx input).outcome.verified

theorem run_trace_valid {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    @Graph.ValidTrace P C ctx (run C ctx input).trace :=
  (run C ctx input).traceValid

theorem run_total {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx) :
    ∃ result : ExecutionResult C ctx,
      result.outcome.Valid ∧ @Graph.ValidTrace P C ctx result.trace :=
  ⟨run C ctx input, run_verified C ctx input, run_trace_valid C ctx input⟩

theorem run_deterministic {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (input : Input C ctx)
    (left right : ExecutionResult C ctx)
    (leftIsRun : left = run C ctx input)
    (rightIsRun : right = run C ctx input) : left = right :=
  leftIsRun.trans rightIsRun.symm

/-- A fully bounded and labeled aggregate whose exact lower mass fits its
exact upper capacity must take CT14's capacity-residual branch.  Graph
profiles only need to prove these semantic premises; they do not need to
repeat the reference runner's control-flow proof. -/
theorem run_terminal_capacity_of_complete {P : Core.Problem}
    (C : Capability P) (ctx : Core.BranchContext P) (input : Input C ctx)
    (bounded : ∀ member, ∃ value, C.memberCapacity ctx member = some value)
    (labeled : ∀ member, ∃ label, C.memberLabel ctx member = some label)
    (within : lowerMass C ctx ≤ upperCapacity C ctx) :
    (run C ctx input).terminal = .capacity := by
  let lower : LowerMassState C ctx := ⟨lowerMass C ctx, rfl⟩
  cases scanned : scanMembers C ctx lower with
  | unbounded residual =>
      obtain ⟨value, present⟩ := bounded residual.member
      have : (some value : Option Nat) = none := present.symm.trans residual.missing
      cases this
  | missingLabel residual =>
      obtain ⟨label, present⟩ := labeled residual.member
      have : (some label : Option C.Label) = none := present.symm.trans residual.missing
      cases this
  | complete scan =>
      cases compared : compare C ctx (computeLedger C ctx scan) with
      | exceeds certificate =>
          have lowerEq : certificate.lower = lowerMass C ctx := certificate.lowerExact
          have upperEq : certificate.upper = upperCapacity C ctx := certificate.upperExact
          have impossible : upperCapacity C ctx < lowerMass C ctx := by
            simpa [lowerEq, upperEq] using certificate.exceeds
          exact (Nat.not_lt_of_ge within impossible).elim
      | within residual =>
          simp [run, runReference, lower, scanned, compared]

/-- The capacity branch has a unique framework trace. -/
theorem run_trace_capacity_of_complete {P : Core.Problem}
    (C : Capability P) (ctx : Core.BranchContext P) (input : Input C ctx)
    (bounded : ∀ member, ∃ value, C.memberCapacity ctx member = some value)
    (labeled : ∀ member, ∃ label, C.memberLabel ctx member = some label)
    (within : lowerMass C ctx ≤ upperCapacity C ctx) :
    (run C ctx input).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] := by
  have terminal := run_terminal_capacity_of_complete C ctx input bounded labeled within
  generalize resultEquation : run C ctx input = result at terminal ⊢
  cases result with
  | mk resultTerminal path outcome =>
      dsimp only at terminal
      subst resultTerminal
      exact Graph.trace_eq_of_path_to_capacity path

/-- If every member has exactly one of two distinct labels, their CT14
multiplicities partition the declared finite universe. -/
theorem multiplicity_add_eq_card_of_binary_labels {P : Core.Problem}
    (C : Capability P) (ctx : Core.BranchContext P)
    (first second : C.Label) (distinct : first ≠ second)
    (exhaustive : ∀ member,
      C.memberLabel ctx member = some first ∨
        C.memberLabel ctx member = some second) :
    multiplicity C ctx first + multiplicity C ctx second = C.members.card := by
  let firstStep := fun (count : Nat) (member : C.Member) =>
    match C.memberLabel ctx member with
    | some found =>
        match C.labelDecidableEq found first with
        | .isTrue _ => count + 1
        | .isFalse _ => count
    | none => count
  let secondStep := fun (count : Nat) (member : C.Member) =>
    match C.memberLabel ctx member with
    | some found =>
        match C.labelDecidableEq found second with
        | .isTrue _ => count + 1
        | .isFalse _ => count
    | none => count
  have auxiliary : ∀ (values : List C.Member) (left right : Nat),
      values.foldl firstStep left + values.foldl secondStep right =
        left + right + values.length := by
    intro values
    induction values with
    | nil => intro left right; simp
    | cons member tail ih =>
        intro left right
        rcases exhaustive member with firstLabel | secondLabel
        · cases selfDecision : C.labelDecidableEq first first with
          | isFalse notSelf => exact (notSelf rfl).elim
          | isTrue selfProof =>
              cases otherDecision : C.labelDecidableEq first second with
              | isTrue equal => exact (distinct equal).elim
              | isFalse notEqual =>
                  simp only [List.foldl_cons]
                  simp [firstStep, secondStep, firstLabel, selfDecision,
                    otherDecision]
                  simpa only [List.length_cons, Nat.add_assoc,
                    Nat.add_left_comm, Nat.add_comm] using ih (left + 1) right
        · cases selfDecision : C.labelDecidableEq second second with
          | isFalse notSelf => exact (notSelf rfl).elim
          | isTrue selfProof =>
              cases otherDecision : C.labelDecidableEq second first with
              | isTrue equal => exact (distinct equal.symm).elim
              | isFalse notEqual =>
                  simp only [List.foldl_cons]
                  simp [firstStep, secondStep, secondLabel, selfDecision,
                    otherDecision]
                  simpa only [List.length_cons, Nat.add_assoc,
                    Nat.add_left_comm, Nat.add_comm] using ih left (right + 1)
  unfold multiplicity
  change C.members.orderedValues.foldl firstStep 0 +
      C.members.orderedValues.foldl secondStep 0 = C.members.card
  simpa using auxiliary C.members.orderedValues 0 0

/-- Boolean reflection of one concrete CT14 member label. -/
def labelMatches {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (label : C.Label) (member : C.Member) : Bool :=
  match C.memberLabel ctx member with
  | some found =>
      match C.labelDecidableEq found label with
      | .isTrue _ => true
      | .isFalse _ => false
  | none => false

@[simp]
theorem labelMatches_eq_true_iff {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (label : C.Label) (member : C.Member) :
    labelMatches C ctx label member = true ↔
      C.memberLabel ctx member = some label := by
  unfold labelMatches
  cases foundEq : C.memberLabel ctx member with
  | none => simp
  | some found =>
      cases labelEq : C.labelDecidableEq found label with
      | isTrue equal => simp [labelEq, equal]
      | isFalse notEqual => simp [labelEq, notEqual]

/-- Unordered view of the exact members carrying one concrete label. -/
def membersWithLabel {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (label : C.Label) : Finset C.Member := by
  letI : DecidableEq C.Member := C.members.decEq
  exact C.members.orderedValues.toFinset.filter fun member =>
    labelMatches C ctx label member

/-- CT14's executable multiplicity fold is exactly the cardinality of the
corresponding filtered member finset.  Downstream candidate fibres can use the
finset view without repeating the runner's fold semantics. -/
theorem card_membersWithLabel_eq_multiplicity {P : Core.Problem}
    (C : Capability P) (ctx : Core.BranchContext P) (label : C.Label) :
    (membersWithLabel C ctx label).card = multiplicity C ctx label := by
  let step := fun (count : Nat) (member : C.Member) =>
    match C.memberLabel ctx member with
    | some found =>
        match C.labelDecidableEq found label with
        | .isTrue _ => count + 1
        | .isFalse _ => count
    | none => count
  have fold_eq : ∀ (values : List C.Member) (count : Nat),
      values.foldl step count =
        count + (values.filter fun member =>
          labelMatches C ctx label member).length := by
    intro values
    induction values with
    | nil => intro count; simp
    | cons member tail ih =>
        intro count
        cases foundEq : C.memberLabel ctx member with
        | none =>
            simp [step, labelMatches, foundEq, ih]
        | some found =>
            cases labelEq : C.labelDecidableEq found label with
            | isTrue equal =>
                subst found
                simp [step, labelMatches, foundEq, labelEq, ih,
                  Nat.add_assoc, Nat.add_comm]
            | isFalse notEqual =>
                simp [step, labelMatches, foundEq, labelEq, ih]
  letI : DecidableEq C.Member := C.members.decEq
  have nodup := C.members.nodup_orderedValues
  unfold membersWithLabel multiplicity
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup (nodup.filter _)]
  change (C.members.orderedValues.filter
      (fun member => labelMatches C ctx label member)).length =
    C.members.orderedValues.foldl step 0
  simpa only [Nat.zero_add] using (fold_eq C.members.orderedValues 0).symm

theorem outcome_exhaustive {P : Core.Problem} {C : Capability P}
    {ctx : Core.BranchContext P} (result : ExecutionResult C ctx) :
    result.terminal = .unbounded ∨
      result.terminal = .missingLabel ∨
      result.terminal = .aggregate ∨
      result.terminal = .capacity := by
  cases result with
  | mk _ _ outcome =>
    cases outcome with
    | unbounded _ => exact Or.inl rfl
    | missingLabel _ => exact Or.inr (Or.inl rfl)
    | aggregate _ => exact Or.inr (Or.inr (Or.inl rfl))
    | capacity _ => exact Or.inr (Or.inr (Or.inr rfl))

end StructuralExhaustion.CT14
