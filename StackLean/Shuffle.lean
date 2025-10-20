import Init.Data.List
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.AllAny
import Aesop
import Mathlib.Tactic.Linarith

import StackLean.Definitions
import StackLean.LSet
import StackLean.Util

--- Stack Classification ---

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
abbrev input_contains_all_target_vars (input : Stack) (target : Target) : Prop
  := target.vars ⊆ input.vars

instance (input : Stack) (target : Target) : Decidable (input_contains_all_target_vars input target) :=
  inferInstanceAs (Decidable (target.vars ⊆ input.vars))

-- The distance from a stack to a target is a metric should decrease at every shuffle step
def distance (stack : Stack) (target : Target) : ℕ :=
  let compare (l : Stack) (r : Stack) : ℕ
    := l
    |> List.zip r
    |> List.map (λ (l,r) => if l = r then 0 else 1)
    |> List.sum

  let deficit := (Int.ofNat stack.length - Int.ofNat target.size).natAbs
  -- TODO: use List.diff
  let args_wrong := compare (stack.args target) (target.args.drop (target.size - stack.length))
  let tail_difference := (target.liveOut - (stack.tail_region target).vars).count

  deficit + args_wrong + tail_difference

--- Shuffling ---

inductive ShuffleResult (start : Stack) where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (finish : Stack) (trace : Trace start finish)
  deriving Repr

theorem args_is_correct_eq (stack : Stack) (target : Target) (hargs : args_is_correct stack target) : stack.args target = target.args := by
  obtain ⟨hsz, _⟩ := hargs
  unfold Stack.args
  split_ifs with h
  · exfalso; linarith [h, hsz]
  · apply List.ext_getElem
    all_goals grind only [= List.length_take, = List.getElem_take, = Nat.min_def]

-- if the args are correct, and at least one arg is still required in the tail,
-- then target.liveOut.count must be > 0.
theorem args_correct_required_tail_out_size
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
      rw [args_is_correct_eq]; unfold args_is_correct; exact hargs
    have (s : Slot) : List.count s (stack.args target) ≤ List.count s stack := by
      apply List.Sublist.count_le; apply stack_args_sublist_stack

    have : ∃ v, v ∈ target.liveOut := by
      simp [more_needed_on_stack, Stack.total_count, Target.min_count] at hmnv
      cases' v <;> grind only

    exact List.length_pos_iff_exists_mem.mpr this

mutual

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) (_ : input_contains_all_target_vars stack target) : ShuffleResult stack
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
          have : (state.args target).length = target.args.length := by simp_all; grind only
          have : 0 < target.liveOut.count := args_correct_required_tail_out_size state target hargs hreq
          have : target.args.length + target.liveOut.count ≤ target.size := target.size.property
          have : target.args.length < state.length := by omega
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
    if hcan_pop : input_contains_all_target_vars state.tail target then

      -- pop always decreases the distance
      have : distance (List.tail state) target < distance state target := by
        simp_all [distance]; split_ifs with hsz
        · refine Nat.lt_of_add_lt_add_right _
        · refine Nat.lt_of_add_lt_add_right _

      -- apply the pop and recurse
      shuffle.go start (.Pop (by grind) trace) target
    else
      .StackTooDeep

  else
    .StackTooDeep
  termination_by (distance state target)

end

--- Correctness ---

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

-- shuffle.go always produces a correct result for all inputs where the
-- starting stack contains all variables required by the target
theorem shuffle_go_correct
  (start : Stack) (state : Stack) (trace : Trace start state) (target : Target)
  (_ : input_contains_all_target_vars start target)
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
  (start : Stack) (target : Target)
  (hvars : input_contains_all_target_vars start target)
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
