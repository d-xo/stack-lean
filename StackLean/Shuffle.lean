import Init.Data.List
import Mathlib.Data.Nat.Basic
import Aesop

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
  let args_wrong := compare (stack.args target) (target.args.drop (target.size - stack.length))
  let tail_difference := (target.liveOut - (stack.tail_region target).vars).count

  deficit + args_wrong + tail_difference

--- Shuffling ---

inductive ShuffleResult (start : Stack) where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (finish : Stack) (trace : Trace start finish)
  deriving Repr

mutual

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) (_ : input_contains_all_target_vars stack target) : ShuffleResult stack
  := shuffle.go stack (.Lit stack) target

@[simp]
def shuffle.go (start : Stack) (trace : Trace start state) (target : Target) : ShuffleResult start :=
  if args_is_correct state target then
    if tail_is_compatible state target
    then .ResultStack state trace
    else .StackTooDeep

  -- if we have too much stuff
  else if hlen : state.length > target.size then
    -- and the head is not needed in the target
    if hcan_pop : input_contains_all_target_vars state.tail target then

      -- pop always decreases the distance
      have : distance (List.tail state) target < distance state target := by
        simp_all [distance]; split_ifs with hsz <;> refine Nat.lt_of_add_lt_add_right _

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
