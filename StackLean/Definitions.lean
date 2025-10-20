import Init.Data.List.Lemmas
import Init.Data.List.Nat.Sublist
import Init.Data.List.Nat.TakeDrop
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Basic
import Aesop

import StackLean.LSet
import StackLean.Util

--- Basic Types ---

abbrev Word := Fin (2 ^ 256)

--- Stack Slots ---

-- A var is a newtype around a Nat
abbrev Var := ℕ

-- In addition to variables, slots can contain literals and junk elems
inductive Slot where
  | Var : Var → Slot
  | Lit : Word → Slot
  | Junk : Slot
  deriving DecidableEq, Repr

instance : LawfulBEq Var := inferInstance
instance : LawfulBEq Slot := inferInstance

def slotToVar : Slot → Option Var
  | .Var v => some v
  | _ => none

--- Stacks ---

abbrev Stack := List Slot

def List.vars (stack : Stack) : LSet Var := stack |> List.filterMap slotToVar |> LSet.ofList

--- Targets ---

-- A target is a specification of a desired shuffle outcome
structure Target where
  -- a concrete args section that must have a specific order and multiplicity
  args : Stack
  -- an abstract tail section that is a set of variables that must remain live for downstream ops
  liveOut : LSet Var
  -- the size of the target stack
  size : { n : ℕ // n ≥ args.length + liveOut.count }

def Target.vars (target : Target) : LSet Var := target.args.vars ∪ target.liveOut

@[simp]
abbrev Target.tail_length (target : Target) := target.size - target.args.length

--- Stack Args ---

@[simp, reducible]
def Stack.args (stack : Stack) (target : Target) : Stack :=
  if stack.length > target.size
  then
    stack
      -- drop the excess
      |> List.drop (stack.length - target.size)
      -- take the args
      |> List.take target.args.length
  else
    -- take whatever stack region we have above the tail
    stack.take (stack.length - target.tail_length)

@[simp]
abbrev example_target (args_sz : ℕ) (total_sz : ℕ) (hsz : total_sz ≥ args_sz := by omega) : Target
  := ⟨List.replicate args_sz (.Lit 1), LSet.ofList [], ⟨total_sz, by simp [LSet.ofList]; grind⟩⟩

example : Stack.args [.Lit 3, .Lit 4, .Lit 5] (example_target 2 4) = [.Lit 3]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 3) = [.Lit 3, .Lit 4]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 4) = [.Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 2) = [.Lit 4, .Lit 5]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 5) = [.Lit 1, .Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 6) = [.Lit 1]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 7 10) = [.Lit 1, .Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 10) = []
  := by simp_all [Stack.args]

@[simp]
theorem args_le_target_args (stack : Stack) (target : Target)
  : (stack.args target).length ≤ target.args.length := by
    simp_all [Stack.args]
    grind only [= List.length_drop, = List.length_take, = Nat.min_def, cases Or]

-- if we prepend the target args any base with length ≤ the tail length, and
-- then take the args of that stack relative to the target, the result is the target.args
theorem args_concat_base_leq
  (base : Stack) (target : Target) (hsz : base.length ≤ target.tail_length)
    : let input := target.args ++ base
      input.args target = target.args.take (input.length - target.tail_length)
  := by
    simp_all [Stack.args]
    split_ifs
    · grind
    · simp_all

-- if we prepend the target args any base with length = the tail length, and
-- then prepend any stack to that, the args of the result relative to the target is the target.args
theorem args_concat_top_base_eq
  (top : Stack) (base : Stack) (target : Target) (hsz : base.length = target.tail_length)
    : let input := top ++ target.args ++ base
      input.args target = target.args
  := by
    simp_all [Stack.args]
    split_ifs
    · have :
        (top.length +
          (target.args.length + (↑target.size - target.args.length))
        - ↑target.size) = top.length := by grind
      simp_all
    · have : top.length = 0 := by omega
      simp_all

--- Stack Tail ---

@[simp, reducible]
def Stack.tail_region (stack : Stack) (target : Target) : Stack :=
    if stack.length > target.size
    then
      -- drop the excess and the args
      stack.drop ((stack.length - target.size) + target.args.length)
    else
      -- drop whatever stack region we have above the tail
      let tail_length := target.size - target.args.length
      stack.drop (stack.length - tail_length)

example : Stack.tail_region [.Lit 3, .Lit 4, .Lit 5] (example_target 2 4) = [.Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 3) = [.Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 4) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 2) = []
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 5) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 6) = [.Lit 2, .Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 7 10) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 10) = [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

theorem stack_tail_le_target_tail_length (stack : Stack) (target : Target) : (stack.tail_region target).length ≤ target.tail_length := by
  simp_all [Stack.tail_region]
  split_ifs <;> grind only [= List.length_drop, cases Or]

theorem stack_tail_eq_stack_length_leq_tail_length
  (stack : Stack) (target : Target)
  (hlen : stack.length ≤ target.tail_length)
    : stack.tail_region target = stack := by
  simp_all [Stack.tail_region]
  intro hsz
  grind

theorem stack_tail_eq_stack_length_gt_tail_length
  (stack : Stack) (target : Target)
  (hlen : stack.length > target.tail_length)
    : stack.tail_region target = stack.drop (stack.length - target.tail_length) := by
  simp_all [Stack.tail_region]
  intro hsz
  grind

--- Traces ---

-- A Trace is evidence of a valid sequence of operations transforming one stack into another
-- It relates an input stack to the set of all stacks reachable from it
inductive Trace : Stack → Stack → Prop where
  | Lit
    : (s : Stack)
    → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap 0 idx)
  | Dup
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev[idx - 1] :: prev)
  | Pop
    : (hlen : 0 < prev.length)
    → Trace start prev
    → Trace start prev.tail
  | Push
    : (w : Word)
    → Trace start prev
    → Trace start (.Lit w :: prev)
  | MarkJunk
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → Trace start prev
    → Trace start (prev.set idx .Junk)

-- apply theorems --

-- applying dup to any trace grows the length of the result by one
theorem dup_grows_stack_by_one
  (start : Stack) (stack : Stack) (trace : Trace start stack)
  (idx : ℕ) (hlen : idx < stack.length) (hlo : 1 ≤ idx) (hhi : idx < 17) :
    let result : Stack := _
    let _ : Trace start result := trace |> .Dup idx hlen hlo hhi
    result.length = stack.length + 1
  := by simp


-- applying swap at the same idx twice to any stack is a noop
theorem apply_swap_inv
  (start : Stack) (stack : Stack) (trace : Trace start stack)
  (idx : ℕ) (hlen : idx < stack.length) (hlo : 1 ≤ idx) (hhi : idx < 17) :
    let result : Stack := _
    let _ : Trace start result
      := trace
      |> .Swap idx hlen hlo hhi
      |> .Swap idx (by simp [List.swap]; omega) (by omega) (by omega)
    stack = result
  := by
    simp_all [List.swap, List.getElem_set]
    split_ifs
    · simp_all
    · ext i; grind
