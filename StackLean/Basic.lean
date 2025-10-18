import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Nodup
import Init.Data.Vector.Basic
import Init.Data.Nat
import Aesop
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Finset.Fold

--- Basic Types ---

abbrev Word := Fin (2 ^ 256)

--- Sets ---

-- We use a subtype here since it's more friendly to computable iteration than the mathlib sets
def LSet (α : Type) := { l : List α // List.Nodup l }

instance : EmptyCollection (LSet α) where
  emptyCollection := ⟨[], by simp⟩

instance [DecidableEq α] : Membership α (LSet α) where
  mem (t : LSet α) (v : α) := v ∈ t.val

instance (t : LSet α) (v : α) [DecidableEq α] : Decidable (v ∈ t) :=
  inferInstanceAs (Decidable (v ∈ t.val))

def LSet.toFinset (ls : LSet α) : Finset α := ⟨ls.val, by simp [ls.property]⟩

instance : HasSubset (LSet α) where
  Subset l r := List.Subset l.val r.val

instance (l r : LSet α) [DecidableEq α] : Decidable (l ⊆ r) :=
  inferInstanceAs (Decidable (l.toFinset ⊆ r.toFinset))

instance [DecidableEq α] : Sub (LSet α) where
  sub (lhs : LSet α) (rhs : LSet α) : LSet α :=
    ⟨lhs.val.filter (· ∉ rhs.val)
    , by
      apply List.Nodup.filter
      exact lhs.property
    ⟩

def LSet.ofList [DecidableEq α] : (vs : List α) → LSet α
  | .nil => ⟨[], by simp⟩
  | .cons hd tl =>
      let rest := LSet.ofList tl
      if helem : hd ∈ rest
      then rest
      else
      ⟨
        hd :: rest.val,
        by
          simp ;
          apply And.intro
          · trivial
          · apply rest.property
      ⟩

instance [DecidableEq α] : Union (LSet α) where
  union l r := LSet.ofList (l.val ++ r.val)

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
  | .Lit _ => none
  | .Junk => none

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
  size : { n : ℕ // n ≥ args.length + liveOut.val.length }

def Target.vars (target : Target) : LSet Var := target.args.vars ∪ target.liveOut

--- Traces ---

inductive Trace where
  | Lit : (stk : Stack) → Trace
  | Swap : ℕ → Trace → Trace
  | Dup : ℕ → Trace → Trace
  | Pop : Trace → Trace
  | Push : Word → Trace → Trace
  | MarkJunk : ℕ → Trace → Trace
  deriving Repr

def Trace.start : Trace → Stack
  | .Lit s => s
  | .Swap _ t => t.start
  | .Dup _ t => t.start
  | .Pop t => t.start
  | .Push _ t => t.start
  | .MarkJunk _ t => t.start

def List.swap {α : Type u} (xs : List α) (i j : ℕ) (hi : i < xs.length := by get_elem_tactic) (hj : j < xs.length := by get_elem_tactic) := (xs.set i xs[j]).set j xs[i]

inductive Trace.valid : Trace → Stack → Prop where
  | Lit : Trace.valid (.Lit s) s
  | Swap
    : Trace.valid s res
    → (hlen : res.length > idx)
    → (hlo : 0 < idx)
    → (hhi : idx < 17)
    → Trace.valid (.Swap idx s) (res.swap 0 idx)
  | Dup
    : Trace.valid s res
    → (hlen : idx < res.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace.valid (.Dup idx s) (res[idx] :: res)
  | Pop
    : Trace.valid s res
    → (hlen : 0 < res.length)
    → Trace.valid (.Pop s) res.tail
  | Push
    : Trace.valid s res
    → Trace.valid (.Push word s) (.Lit word :: res)
  | MarkJunk
    : Trace.valid s res
    → (hlen : idx < res.length)
    → Trace.valid (.MarkJunk idx s) (res.set idx .Junk)


-- apply theorems --

-- dup grows stack size by 1
theorem apply_dup_grows_stack (stack : Stack) (idx : ℕ) (heval : Trace.valid (.Dup idx (.Lit stack)) res) : res.length = stack.length + 1 := match heval with
  | .Dup .Lit hlen hlo hhi => by simp_all


-- applying swap at the same idx twice is a noop
theorem apply_swap_inv (stack : Stack) (idx : ℕ) (heval : Trace.valid (.Lit stack |> .Swap idx |> .Swap idx) res) : res = stack := match heval with
  | .Swap (.Swap .Lit hlen' hlo' hhi') hlen hlo hhi => by
    simp_all [List.swap, List.getElem_set]
    split_ifs
    · simp_all
    · ext i
      simp_all [List.getElem?_set]
      split_ifs <;> simp_all
      exact List.getElem_eq_iff ?_

--- Stack Shuffling ---


@[simp]
abbrev stack_is_large_enough (stack : Stack) (target : Target) : Prop := stack.length ≥ target.args.length + target.liveOut.val.length

@[simp]
abbrev args_is_correct (stack: Stack) (target : Target) : Prop :=
  have hidx : (hle : stack_is_large_enough stack target) -> ∀ i, i < target.args.length → i < stack.length := by omega
  have thidx : ∀ i, i < target.args.length → i < target.args.length := by omega

  (stack_is_large_enough stack target) ∧ ((hle : stack_is_large_enough stack target) → ∀ (i : ℕ), (hn : i < target.args.length) → stack[i]'(hidx hle i hn) = target.args[i]'(thidx i hn))

@[simp]
abbrev tail_is_compatible (stack: Stack) (target : Target) : Prop :=
  ∀ (v : Var), v ∈ target.liveOut → (.Var v) ∈ stack.drop target.args.length

@[simp]
abbrev is_compatible (stack: Stack) (target : Target) : Prop :=
  (stack_is_large_enough stack target) ∧ (args_is_correct stack target) ∧ (tail_is_compatible stack target)

def distance (stack : Stack) (target : Target) : ℕ :=
  let compare (l : Stack) (r : Stack) : ℕ
    := l
    |> List.zip r
    |> List.map (λ (l,r) => if l = r then 0 else 1)
    |> List.sum

  let deficit := (Int.ofNat stack.length - Int.ofNat target.size).natAbs

  let args_wrong :=
    if stack.length < target.size then
      target.args |> List.drop (target.size - stack.length) |> compare stack
    else
      stack |> List.drop (stack.length - target.size) |> List.take target.args.length |> compare target.args

  let dropLen :=
    if stack.length < target.size
    then stack.length - (target.size - target.args.length)
    else target.args.length + (stack.length - target.size)
  let tailVars := stack |> List.drop (dropLen) |> List.vars
  let tail_difference := (target.liveOut - tailVars).val.length

  deficit + args_wrong + tail_difference

#eval distance [.Var 42, .Var 55, .Var 66] (Target.mk [.Var 42, .Var 55, .Var 66] (LSet.ofList [42]) ⟨10, by simp[LSet.ofList]; aesop⟩)

@[simp]
abbrev input_contains_all_target_vars (input : Stack) (target : Target) : Prop := target.vars ⊆ input.vars

instance (input : Stack) (target : Target) : Decidable (input_contains_all_target_vars input target) :=
  inferInstanceAs (Decidable (target.vars ⊆ input.vars))

inductive ShuffleResult where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (trace : Trace) (finish : Stack) (valid : Trace.valid trace finish)
  deriving Repr

mutual

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) (precondition : input_contains_all_target_vars stack target) : ShuffleResult
  := shuffle.go (.Lit stack) .Lit target

@[simp]
def shuffle.go  (trace : Trace) (valid : Trace.valid trace state) (target : Target) : ShuffleResult :=
  if args_is_correct state target then
    if tail_is_compatible state target
    then .ResultStack trace _ valid
    else .StackTooDeep

  -- if we have too much stuff
  else if hlen : state.length > target.size then
    if hcan_pop : input_contains_all_target_vars state.tail target then
      have : distance (List.tail state) target < distance state target := by
        clear hcan_pop; simp [distance]; split_ifs <;> grind
      shuffle.go (.Pop trace) (.Pop valid (by omega)) target
    else
      .StackTooDeep

  else
    .StackTooDeep
  termination_by (distance state target)


-- def shuffleStep_dupMissingTailElement (stack : Stack) (target : Target) : ShuffleResult :=
--   if false
--   then shuffle stack target
--   else .StackTooDeep

end

-- #eval shuffle [.Var 33, .Var 33, .Var 33] (Target.mk [.Var 33, .Var 33] (LSet.ofList [33]) ⟨3, by simp[LSet.ofList]; aesop⟩)

-- for every stack and target
theorem shuffle_correct (stack : Stack) (target : Target) (hvars : input_contains_all_target_vars stack target) :
   -- the result of a shuffle is either:
   match shuffle stack target hvars with
     -- a valid sequence of ops from the input to a result stack compatible with the target
     | .ResultStack trace finish valid => trace.start = stack ∧ is_compatible finish target
     -- a stack too deep
     | .StackTooDeep => True
     -- we never enter the forbidden state
     | .ForbiddenState => False
   := by
      unfold shuffle
      induction stack with
      | nil => simp [shuffle.go]; split_ifs <;> simp_all [Trace.start]
      | cons hd tl ih =>
        unfold shuffle.go
        split_ifs with hargs htail hsz hcan_pop
        · simp [Trace.start]; grind
        · simp
        ·
          sorry
        · simp
        · simp

      --split_ifs with hargs htail
      --· simp_all [Trace.start]
      --· simp
      --· induction stack with
        --| nil =>
          --simp [shuffle.go]
          --split_ifs <;> simp_all
        --| cons hd tl ih =>

      --· simp
