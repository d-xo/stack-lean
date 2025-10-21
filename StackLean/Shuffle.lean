import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.AllAny
import Aesop
import Mathlib.Tactic.Linarith

import StackLean.Definitions
import StackLean.LSet
import StackLean.Util

set_option profiler true


--- Stack Classification ---------------------------------------------------------------------------


@[simp]
abbrev size_is_correct (stack : Stack) (target : Target) : Prop
  := stack.length = target.size

@[simp]
abbrev args_is_correct (stack: Stack) (target : Target) : Prop :=
  (size_is_correct stack target) ∧ ((hsz : size_is_correct stack target) →
    have : target.size ≥ target.args.length + target.liveOut.count := target.size.property
    ∀ (i : ℕ), (hn : i < target.args.length) → stack[i] = target.args[i]
  )

@[simp]
abbrev tail_is_compatible (stack: Stack) (target : Target) : Prop :=
  (size_is_correct stack target) ∧ ((hsz : size_is_correct stack target) →
    ∀ (v : Var), v ∈ target.liveOut → (.Var v) ∈ stack.drop target.args.length
  )

@[simp]
-- Do we have a sufficient quantity of slot?
abbrev more_needed_on_stack (stack: Stack) (target : Target) (slot : Slot) : Prop :=
  stack.total_count slot < target.min_count slot

@[simp]
-- Are any of the stack args required in the tail but not there yet?
abbrev any_arg_required_in_tail {hargs : args_is_correct stack target} (stack: Stack) (target : Target) : Prop :=
  (stack.args target).any (λ arg => more_needed_on_stack stack target arg)

@[simp]
-- a target is reachable from a stack if the stack contains all variables needed in the target
abbrev reachable (stack : Stack) (target : Target) : Prop
  := target.vars ⊆ stack.vars

instance (stack : Stack) (target : Target) : Decidable (reachable stack target) :=
  inferInstanceAs (Decidable (target.vars ⊆ stack.vars))


-- Termination Measure -----------------------------------------------------------------------------


-- the difference between the size of the stack and target
def size_deficit (stack : Stack) (target : Target) : ℕ
  := (Int.ofNat stack.length - Int.ofNat target.size).natAbs

-- how many things do we need in the target that are still missing in the stack
def required_missing (stack : Stack) (target : Target) : ℕ
  := target.elems.val.foldl (λ a v => a + (stack.count v - target.min_count v)) 0

-- how many args are out of place
def incorrect_args (stack : Stack) (target : Target) : ℕ
  := (stack.args target)
      |> List.diff (target.args.drop (target.size - stack.length))
      |> List.length

-- how many elements are required in the tail but not there yet
def tail_difference (stack : Stack) (target : Target) : ℕ
  := (target.liveOut - (stack.tail_region target).vars).count

@[simp]
-- The distance from a stack to a target is a metric should decrease at every shuffle step
def distance (stack : Stack) (target : Target) : ℕ
  := (size_deficit stack target)
   + (required_missing stack target)
   + (incorrect_args stack target)
   + (tail_difference stack target)


-- Lemmas ------------------------------------------------------------------------------


-- if the args are correct, then stack.args = target.args
lemma correct_args_stack_eq_target (stack : Stack) (target : Target) (hargs : args_is_correct stack target)
    : stack.args target = target.args
  := by
    obtain ⟨hsz, _⟩ := hargs
    unfold Stack.args
    split_ifs with h
    · exfalso; linarith [h, hsz]
    · apply List.ext_getElem
      all_goals grind only [= List.length_take, = List.getElem_take, = Nat.min_def]

-- if the args are correct, and at least one arg is still required in the tail,
-- then target.liveOut.count must be > 0.
lemma args_correct_required_tail_out_size
  (stack : Stack) (target : Target)
  (hargs : args_is_correct stack target) (hreq : any_arg_required_in_tail (hargs := hargs) stack target)
    : target.liveOut.count > 0
  := by
    have ⟨v, ⟨hvmem, hmnv⟩⟩ : ∃ v ∈ (stack.args target), more_needed_on_stack stack target v := by
      rw [←List.any_iff_exists_prop]; exact hreq

    have : 0 < (stack.args target).count v := by
      rw [List.count_pos_iff]; exact hvmem

    have : 0 < stack.count v := by
      grind only [
        List.take_sublist, usr List.Sublist.length_le, =_ List.contains_iff_mem, usr
        List.Sublist.count_le, = List.any_eq, usr List.count_le_length, → List.Sublist.subset, =
        List.count_eq_length_filter, stack_args_sublist_stack
      ]

    have (s : Slot) : List.count s (stack.args target) = List.count s target.args := by
      rw [correct_args_stack_eq_target]; unfold args_is_correct; exact hargs
    have (s : Slot) : List.count s (stack.args target) ≤ List.count s stack := by
      apply List.Sublist.count_le; apply stack_args_sublist_stack

    have : ∃ v, v ∈ target.liveOut := by
      simp [more_needed_on_stack, Stack.total_count, Target.min_count] at hmnv
      cases' v <;> grind only

    exact List.length_pos_iff_exists_mem.mpr this

-- the preconditions for a pop are sufficient to decrease the distance
lemma pop_decreasing
  (hlen : stack.length > target.size) (hcan_pop : stack.tail.count stack[0] ≥ target.min_count stack[0])
    : distance stack.tail target < distance stack target
  := by
    unfold distance
    have : size_deficit stack.tail target < size_deficit stack target := by
      simp +arith [size_deficit]; omega

    have : required_missing stack.tail target = required_missing stack target := by
      match stack[0] with
        | .Var v =>
          unfold required_missing
          sorry

    have : incorrect_args stack.tail target = incorrect_args stack target := by
      simp +arith [incorrect_args]
      split_ifs with h
      · sorry
      · have h1 : ↑target.size = List.length stack - 1 := by omega
        have h2 : (stack.length - 1) - (stack.length - 1) = 0 := by omega
        have h3 : (stack.length - 1) - stack.length = 0 := by omega
        have h4 : stack.length - (stack.length - 1) = 1 := by omega
        rw [h1, h2, h3, h4]
        simp only [List.drop_zero, List.drop_one]
        grind only [cases Or]

    have : tail_difference stack.tail target = tail_difference stack target := by
      simp [tail_difference]; grind only

    grind only


--- Shuffling --------------------------------------------------------------------------------------


inductive ShuffleResult (start : Stack) where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (finish : Stack) (trace : Trace start finish)
  deriving Repr

mutual

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) (_ : reachable stack target) : ShuffleResult stack
    := shuffle.go stack (.Lit stack) target

@[simp]
def shuffle.go (start : Stack) (trace : Trace start state) (target : Target) : ShuffleResult start :=
  if hargs : args_is_correct state target then
    if hreq : any_arg_required_in_tail state target
    then
      match (state.args target).reverse.findFinIdx? (more_needed_on_stack state target) with
      -- we already validated that at least one arg is required in hreq
      | none => .ForbiddenState
      --
      | some elem_idx =>
        if hidx : elem_idx.val > 15 then
          .StackTooDeep
        else
          -- utility lemmas
          have := args_correct_required_tail_out_size state target hargs hreq
          have := target.size.property
          have : (state.args target).length = target.args.length := by simp_all; grind only
          have : elem_idx < (state.args target).length := (Fin.cast List.length_reverse elem_idx).isLt

          -- termination
          have : distance (state[elem_idx] :: state) target < distance state target := by sorry

          -- dup and recurse
          shuffle.go start (.Dup (elem_idx + 1) (by omega) (by omega) (by omega) trace) target
    else
      .ResultStack state trace

  -- if we have too much stuff
  else if hlen : state.length > target.size then
    -- and the head is not needed in the target
    if hcan_pop : state.tail.count state[0] ≥ target.min_count state[0]
    then
      -- then apply the pop and recurse
      have := pop_decreasing hlen hcan_pop
      shuffle.go start (.Pop (by grind only) trace) target
    else
      .StackTooDeep

  else
    .StackTooDeep
  termination_by (distance state target)

end


--- Correctness ------------------------------------------------------------------------------------


@[simp]
abbrev is_compatible (stack: Stack) (target : Target) : Prop :=
  (size_is_correct stack target) ∧ (args_is_correct stack target) ∧ (tail_is_compatible stack target)

@[simp]
abbrev result_correct (start : Stack) (target : Target) : ShuffleResult start → Prop
  -- CORRECT: a valid sequence of ops from the input to a result stack compatible with the target
  | .ResultStack finish _ => Trace start finish ∧ is_compatible finish target
  -- CORRECT: a stack too deep (TODO: strengthen to ensure that we actually hit std
  | .StackTooDeep => True
  -- INCORRECT: the forbidden state
  | .ForbiddenState => False

/-
-- shuffle.go always produces a correct result for all inputs where the
-- starting stack contains all variables required by the target
theorem shuffle_go_correct
  (start : Stack) (state : Stack) (trace : Trace start state) (target : Target) (_ : reachable start target)
    : result_correct start target (shuffle.go start trace target)
  := by
    induction state with
    | nil =>
      simp [shuffle.go]
      split_ifs <;> grind only [
        List.length_nil,
        =_ List.contains_iff_mem,
        List.drop_nil,
        cases Or
      ]
    | cons hd tl ih =>
      unfold shuffle.go
      split_ifs <;> grind only [
        List.length_cons,
        List.tail_cons,
        = List.getElem_cons,
        =_ List.contains_iff_mem,
        cases Or
      ]

-- shuffle always produces a correct result for all inputs where the
-- starting stack contains all variables required by the target
theorem shuffle_correct
  (start : Stack) (target : Target) (hvars : reachable start target)
    : result_correct start target (shuffle start target hvars)
   := by
      induction start with
      | nil =>
        simp [shuffle, shuffle.go]
        split_ifs
        · constructor; exact (.Lit [])
          grind only [List.length_nil, =_ List.contains_iff_mem, List.drop_nil, cases Or]
        · simp only
        · simp only

      | cons hd tl ih =>
        unfold shuffle
        unfold shuffle.go
        split_ifs with hargs htail hsz hcan_pop <;> try (grind only)
        · constructor; exact (.Lit (hd :: tl))
          grind only [ List.length_cons, = List.getElem_cons, =_ List.contains_iff_mem, cases Or ]
        · refine shuffle_go_correct (hd :: tl) ?_ ?_ target hvars
      -/
