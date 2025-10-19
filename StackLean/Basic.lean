import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Nodup
import Init.Data.Vector.Basic
import Init.Data.Nat
import Aesop
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Finset.Fold

--- Utils ---

def List.swap
  {α : Type u} (xs : List α) (i j : ℕ)
  (hi : i < xs.length := by get_elem_tactic)
  (hj : j < xs.length := by get_elem_tactic)
  := (xs.set i xs[j]).set j xs[i]

--- Sets ---

-- We use a subtype here since it's more friendly to computable iteration than the mathlib sets
def LSet (α : Type) := { l : List α // List.Nodup l }

@[simp]
def LSet.count (s : LSet α) := s.val.length

instance : EmptyCollection (LSet α) where
  emptyCollection := ⟨[], by simp⟩

instance : Membership α (LSet α) where
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

  let args_wrong :=
    if stack.length < target.size then
      target.args |> List.drop (target.size - stack.length) |> compare stack
    else
      stack |> List.drop (stack.length - target.size)
            |> List.take target.args.length
            |> compare target.args

  let dropLen :=
    if stack.length < target.size
    then stack.length - (target.size - target.args.length)
    else target.args.length + (stack.length - target.size)
  let tailVars := stack |> List.drop (dropLen) |> List.vars
  let tail_difference := (target.liveOut - tailVars).count

  deficit + args_wrong + tail_difference

--- Shuffling ---

inductive ShuffleResult (start : Stack) where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (finish : Stack) (trace : Trace start finish)
  deriving Repr

mutual

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) (precondition : input_contains_all_target_vars stack target) : ShuffleResult stack
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
      -- pop
      have : distance (List.tail state) target < distance state target := by
        clear hcan_pop; simp [distance]; split_ifs <;> grind only
      shuffle.go start (.Pop (by omega) trace) target
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
  (hvars : input_contains_all_target_vars start target)
    : result_correct start target (shuffle.go start trace target)
  := by
    induction state with
    | nil =>
      simp [shuffle.go]
      split_ifs <;> grind only [
        List.length_nil,
        =_ List.contains_iff_mem,
        List.drop_nil, cases Or
      ]
    | cons hd tl ih =>
      unfold shuffle.go
      split_ifs <;> try grind only [
        List.length_cons,
        List.tail_cons,
        = List.getElem_cons,
        =_ List.contains_iff_mem,
        cases Or
      ]

-- shuffle always produces a correct result for all inputs where the
-- starting stack contains all variables required by the target
theorem shuffle_correct
  (start : Stack) (target : Target) (hvars : input_contains_all_target_vars start target)
    : result_correct start target (shuffle start target hvars)
   := by
      induction start with
      | nil =>
        simp [shuffle, shuffle.go]
        split_ifs
        · constructor; exact (.Lit [])
          simp_all only [
            input_contains_all_target_vars,
            forall_true_left,
            true_and,
            List.drop_nil,
            List.not_mem_nil,
            imp_false,
            List.length_nil,
            implies_true,
            and_self
          ]
        · simp only []
        · simp only []

      | cons hd tl ih =>
        unfold shuffle
        unfold shuffle.go
        split_ifs with hargs htail hsz hcan_pop <;> try (grind only)
        · constructor; exact (.Lit (hd :: tl))
          simp_all only [
            input_contains_all_target_vars,
            result_correct,
            is_compatible,
            size_is_correct,
            LSet.count,
            args_is_correct,
            tail_is_compatible,
            true_and,
            forall_true_left,
            List.length_cons,
            implies_true,
            and_self
          ]
        · refine shuffle_go_correct (hd :: tl) ?_ ?_ target hvars
