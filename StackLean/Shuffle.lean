import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.AllAny
import Aesop
import Mathlib.Tactic.Linarith

import StackLean.Definitions
import StackLean.Stats
import StackLean.LSet
import StackLean.Util

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

          have hmore : more_needed_on_stack state target state[elem_idx] := by
            grind
            sorry
          let e : Fin state.length := Fin.castLE (by omega) (Fin.cast List.length_reverse elem_idx)

          -- termination
          have : distance (state[elem_idx] :: state) target < distance state target :=
            dup_decreasing state target e hargs hmore

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
