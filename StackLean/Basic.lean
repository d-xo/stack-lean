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

--- Targets ---

-- A target is a specification of a desired shuffle outcome
structure Target where
  -- a concrete args section that must have a specific order and multiplicity
  args : List Slot
  -- an abstract tail section that is a set of variables that must remain live for downstream ops
  liveOut : LSet Var

--- Stacks ---

inductive Stack where
  | Lit : (stk : List Slot) → Stack
  | Swap : Nat → Stack → Stack
  | Dup : Nat → Stack → Stack
  | Pop : Stack → Stack
  | Push : Word → Stack → Stack
  | MarkJunk : Nat → Stack → Stack

inductive Stack.eval : Stack → (List Slot) → Prop where
  | Lit : Stack.eval (.Lit s) s
  | Swap
    : Stack.eval s res
    → (hlen : res.length > idx)
    → (hlo : 0 < idx)
    → (hhi : idx < 17)
    → Stack.eval (.Swap idx s) ((res.set 0 res[idx]).set idx res[0])
  | Dup
    : Stack.eval s res
    → (hlen : idx < res.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Stack.eval (.Dup idx s) (res[idx] :: res)
  | Pop
    : Stack.eval s res
    → (hlen : 0 < res.length)
    → Stack.eval (.Pop s) res.tail
  | Push
    : Stack.eval s res
    → Stack.eval (.Push word s) (.Lit word :: res)
  | MarkJunk
    : Stack.eval s res
    → (hlen : idx < res.length)
    → Stack.eval (.MarkJunk idx s) (res.set idx .Junk)


-- apply theorems --

-- dup grows stack size by 1
theorem apply_dup_grows_stack (stack : List Slot) (idx : Nat) (heval : Stack.eval (.Dup idx (.Lit stack)) res) : res.length = stack.length + 1 := match heval with
  | .Dup .Lit hlen hlo hhi => by simp_all


-- applying swap at the same idx twice is a noop
theorem apply_swap_inv (stack : List Slot) (idx : Nat) (heval : Stack.eval (.Lit stack |> .Swap idx |> .Swap idx) res) : res = stack := match heval with
  | .Swap (.Swap .Lit hlen' hlo' hhi') hlen hlo hhi => by
    simp_all [List.getElem_set]
    split_ifs
    · simp_all
    · ext i
      simp_all [List.getElem?_set]
      split_ifs <;> simp_all
      exact List.getElem_eq_iff ?_

--- Stack Shuffling ---

inductive ShuffleResult where
  | StackTooDeep
  | ForbiddenState
  | ResultStack (start : List Slot) (finish : List Slot) (valid : Stack.eval (.Lit start) finish)

@[simp]
abbrev stack_is_large_enough (stack : List Slot) (target : Target) : Prop := stack.length ≥ target.args.length + target.liveOut.val.length

@[simp]
abbrev args_is_correct (stack: List Slot) (target : Target) : Prop :=
  have hidx : (hle : stack_is_large_enough stack target) -> ∀ i, i < target.args.length → i < stack.length := by omega
  have thidx : ∀ i, i < target.args.length → i < target.args.length := by omega

  (stack_is_large_enough stack target) ∧ ((hle : stack_is_large_enough stack target) → ∀ (i : Nat), (hn : i < target.args.length) → stack[i]'(hidx hle i hn) = target.args[i]'(thidx i hn))

@[simp]
abbrev tail_is_compatible (stack: List Slot) (target : Target) : Prop :=
  ∀ (v : Var), v ∈ target.liveOut → (.Var v) ∈ stack.drop target.args.length

@[simp]
abbrev is_compatible (stack: List Slot) (target : Target) : Prop :=
  (stack_is_large_enough stack target) ∧ (args_is_correct stack target) ∧ (tail_is_compatible stack target)

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : List Slot) (target : Target) : ShuffleResult :=
  if (args_is_correct stack target)
  then
    if (tail_is_compatible stack target)
    then .ResultStack stack stack .Lit
    else .StackTooDeep
  else .StackTooDeep

theorem shuffle_correct : ∀ (stack : List Slot) (target : Target), ∃ (res : ShuffleResult) (rstack : List Slot) (trace : Stack.eval (.Lit stack) rstack),
  res = shuffle stack target → ((.ResultStack stack rstack trace = shuffle stack target ∧ is_compatible rstack target) ∨ .StackTooDeep = res)
    := by
        intros stack target
        exact ⟨.ResultStack stack stack .Lit, stack, .Lit , by
          intro hres
          simp [shuffle]
          simp [shuffle] at hres
          split_ifs with hargs htail <;> simp_all
        ⟩
