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
    → Trace start (prev[idx] :: prev)
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
