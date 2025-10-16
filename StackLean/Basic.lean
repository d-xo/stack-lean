import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Nodup
import Init.Data.Vector.Basic
import Aesop

--- Basic Types ---

abbrev Word := Fin (2 ^ 256)

--- Sets ---

-- We use a subtype here since it's more friendly to computable iteration than the mathlib sets
def LSet (α : Type) := { l : List α // List.Nodup l }

instance : Membership α (LSet α) where
  mem (t : LSet α) (v : α) := v ∈ t.val

instance (t : LSet α) (v : α) [DecidableEq α] : Decidable (v ∈ t) :=
  inferInstanceAs (Decidable (v ∈ t.val))

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

--- Stack Slots ---

-- A var is a newtype around a Nat
def Var := Nat
  deriving DecidableEq

-- In addition to variables, slots can contain literals and junk elems
inductive Slot where
  | Var : Var → Slot
  | Lit : Word → Slot
  | Junk : Slot
  deriving DecidableEq

instance : LawfulBEq Var := inferInstance
instance : LawfulBEq Slot := inferInstance

-- Stacks ---

abbrev Stack (sz : Nat):= { l : List Slot // l.length = sz}


def Stack.vars (s : Stack sz) : LSet Var :=
  let unwrap := λ s =>
    match s with
      | .Var v => some v
      | _ => none

  s.val |> List.filterMap unwrap |> LSet.ofList

--- Targets ---

-- A target is a specification of a desired shuffle outcome
structure Target (nargs : Nat) where
  -- a concrete args section that must have a specific order and multiplicity
  args : Stack nargs
  -- an abstract tail section that is a set of variables that must remain live for downstream ops
  liveOut : LSet Var

def Target.surplus (target : Target nargs) (stack : Stack sz) (slot : Slot) : Prop :=
  let target_args_count := target.args.val.count slot
  let stack_head_count := stack.val |> List.take target.args.val.length |> List.count slot
  match slot with
  | .Var v => target_args_count < stack_head_count ∧ v ∈ target.liveOut
  | .Lit _ => target_args_count < stack_head_count
  | .Junk => True

instance (target : Target nargs) (stack : Stack sz) (slot : Slot) : Decidable (target.surplus stack slot) := by
  unfold Target.surplus
  match slot with
  | .Var v => exact inferInstance
  | .Lit _ => exact inferInstance
  | .Junk => exact isTrue trivial

--- Stack Manipulation ---

-- The operations that can be applied to a stack of a given size
inductive Op : Nat → Type where
  -- swap0 is a noop, the others match the evm
  | Swap : (_ : szin > 0) → Fin (min 17 szin) → Op szin
  -- dupn => evm dup(n + 1)
  | Dup : (_ : szin > 0) → Fin (min 16 szin) → Op szin
  | Pop : (_ : szin > 0) → Op szin
  | Push : Word → Op szin
  | MarkJunk : Fin szin → Op szin

-- The effect an operation has on the size of a stack
@[reducible, simp]
def sizeAfter (_ : Stack szin) (op : Op szin) : Nat := match op with
  | .Swap _ _ => szin
  | .Dup _ _ => szin + 1
  | .Pop _ => szin - 1
  | .Push _ => szin + 1
  | .MarkJunk _ => szin

def Stack.apply (stack : Stack szin) (op : Op szin) : Stack (sizeAfter stack op) :=
  have : stack.val.length = szin := stack.property
  match op with
    | .Swap _ idx =>
        have : idx < stack.val.length := by omega

        let s := stack.val.set 0 stack.val[idx]
        have : s.length = stack.val.length := by simp_all only [Fin.getElem_fin, List.length_set, s]

        ⟨s.set (idx) stack.val[0], by simp_all⟩
    | .Dup _ idx => ⟨stack.val[idx] :: stack.val, by simp_all⟩
    | .Pop _ => ⟨stack.val.tail, by simp_all⟩
    | .Push val => ⟨.Lit val :: stack.val, by simp_all⟩
    | .MarkJunk idx =>
      have : idx < stack.val.length := by omega
      ⟨stack.val.set idx .Junk, by simp_all⟩

-- apply theorems --

-- applying swap at the same idx twice is a noop
theorem apply_swap_inv (sz : Nat) (hsz : sz > 0) (stack : Stack sz) (idx : Fin (min 17 sz)):
  (stack.apply (.Swap hsz idx)).apply (.Swap hsz idx) = stack := by
    simp_all [Stack.apply, List.getElem_set]
    split_ifs
    · simp_all
    · ext i
      simp_all [List.getElem?_set]
      split_ifs <;> simp_all

-- swap does not change the length of the stack
theorem apply_swap_length (sz : Nat) (hsz : sz > 0) (stack : Stack sz) (idx : Fin (min 17 sz)) :
  (stack.apply (.Swap hsz idx)).val.length = sz := by
    simp [Stack.apply, stack.property]

-- swap switches the elem at idx with the elem at 0
theorem apply_swap_positions_switched (sz: Nat) (hsz : sz > 0) (stack : Stack sz) (idx : Fin (min 17 sz)) :
  ∃ (s' : Stack sz), stack.apply (.Swap hsz idx) = s' ∧ s'.val[0] = stack.val[idx] ∧ s'.val[idx]? = some stack.val[0] := by
  have : idx < stack.val.length := by omega
  simp_all [Stack.apply, List.getElem_set]

-- dup grows stack size by 1
theorem apply_dup_grows_stack (sz : Nat) (hsz: sz > 0) (stack : Stack sz) (idx : Fin (min 16 sz)) :
  (stack.apply (.Dup hsz idx)).val.length = (stack.val.length + 1) := by simp [Stack.apply]

-- the stack head is the same as the element at idx after applying (dup idx)
theorem apply_dup_stack_top_eq_idx (sz : Nat) (hsz: sz > 0) (stack : Stack sz) (idx : Fin (min 16 sz)) :
  (stack.apply (.Dup hsz idx)).val[0]'(by simp [Stack.apply]) = (stack.val[idx]) := by simp [Stack.apply]

-- the tail of the new stack is the same as the starting stack after applying (dup idx)
theorem apply_dup_stack_tail_eq_prev (sz : Nat) (hsz : sz > 0) (stack : Stack sz) (idx : Fin (min 16 sz)) :
  (stack.apply (.Dup hsz idx)).val.tail = stack := by simp [Stack.apply]

-- the result of applying pop is the same as the tail of the input stack
theorem apply_pop_eq_prev_stack_tail (sz : Nat) (hsz : sz > 0) (stack : Stack sz) :
  stack.apply (.Pop hsz) = stack.val.tail := by simp [Stack.apply]

-- TODO: push / markjunk theorems

--- Stack Shuffling ---

inductive ShuffleResult where
  | StackTooDeep
  | ForbiddenState
  | ResultStack(sz : Nat)(stack: Stack sz)

@[simp]
abbrev stack_is_large_enough (sz : Nat) (nargs : Nat) (target : Target nargs) : Prop := sz ≥ nargs + target.liveOut.val.length

@[simp]
abbrev args_is_correct (sz : Nat) (stack: Stack sz) (nargs : Nat) (target : Target nargs) : Prop :=
  have : target.args.val.length = nargs := target.args.property
  have : stack.val.length = sz := stack.property
  have hidx : (hle : stack_is_large_enough sz nargs target) -> ∀ i, i < nargs → i < stack.val.length := by omega
  have thidx : ∀ i, i < nargs → i < target.args.val.length := by omega

  (stack_is_large_enough sz nargs target) ∧ ((hle : stack_is_large_enough sz nargs target) → ∀ (i : Nat), (hn : i < nargs) → stack.val[i]'(hidx hle i hn) = target.args.val[i]'(thidx i hn))

@[simp]
abbrev tail_is_compatible (sz : Nat) (stack: Stack sz) (nargs : Nat) (target : Target nargs) : Prop :=
  ∀ (v : Var), v ∈ target.liveOut → (.Var v) ∈ stack.val.drop nargs

@[simp]
abbrev is_compatible (sz : Nat) (stack: Stack sz) (nargs : Nat) (target : Target nargs) : Prop :=
  (stack_is_large_enough sz nargs target) ∧ (args_is_correct sz stack nargs target) ∧ (tail_is_compatible sz stack nargs target)

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (sz : Nat) (stack : Stack sz) (nargs : Nat) (target : Target nargs) : ShuffleResult :=
  if (args_is_correct sz stack nargs target)
  then
    if (tail_is_compatible sz stack nargs target)
    then .ResultStack sz stack
    else .StackTooDeep
  else .StackTooDeep

theorem shuffle_correct : ∀ (stack : Stack sz) (target : Target nargs), ∃ (res : ShuffleResult) (rsz : Nat) (rstack : Stack rsz),
  res = shuffle sz stack nargs target → ((.ResultStack rsz rstack = shuffle sz stack nargs target ∧ is_compatible rsz rstack nargs target) ∨ .StackTooDeep = res)
    := by
        intros stack target
        exact ⟨.ResultStack sz stack, sz, stack , by
          intro hres
          simp [shuffle]
          simp [shuffle] at hres
          split_ifs with hargs htail <;> simp_all
        ⟩
