import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup
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
  simp_all [Stack.apply, List.length_set, List.getElem_set]

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

-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
def shuffle (stack : Stack) (target : Target) : Except Err Stack := do
  if h_stack_empty : stack = [] then
    throw .StackTooShallow
  else

    let head := stack.take target.args.length
    let tail := stack.drop target.args.length

    -- check if the current head matches the target head
    if hargs : head = target.args then
      -- check if any of the args are also required in the tail and not there yet
      let missing := target.liveOut - Stack.vars tail
      for var in missing.val do
        match head.findIdx? (· == .Var var) with
        | .none => continue
        -- dup if that is the case
        | .some idx =>
          if h : idx < 16 then
            let s' ← stack.apply (.Dup ⟨idx, h⟩)
            -- TODO: recurse
            return s'
          else
            throw .StackTooDeep
      -- otherwise return, we are done
      return stack

    else

      -- invariant: the args region is wrong
      have h_wrong : head ≠ target.args := by simp_all
      -- invariant: the args region is non empty
      have h_non_empty : head ≠ [] := by
        by_contra h_empty
        have h_args_empty : target.args = []:= by simp_all [head]
        simp_all

      -- helper lemma for safe indexing proofs
      have : 0 < stack.length := by exact List.length_pos_iff.mpr h_stack_empty

      -- if the top can be popped (args and tail have enough of it without it, it’s not junk)
      if h_top_is_surplus : target.surplus stack stack[0] then
        -- pop it
        let s' ← stack.apply .Pop
        -- TODO: recurse
        return s'
      else

        -- invariant: the top is either required in args or in tail or is junk
        -- TODO: this is a pretty unsatisfying definition...
        have h_top_required_or_junk : ¬(target.surplus stack stack[0]) := by simp_all

        -- if the top is junk and popping it fixes one or more positions in args
        if h_popping_junk_fixes_args : stack[0] = .Junk ∧ True then
          -- pop it
          let s' ← stack.apply .Pop
          -- TODO: recurse
          return s'
        else

          -- TODO: if the top is out of position and required in args, swap it to the right place
          -- TODO: invariant: the top is in position or belongs in the tail

          -- TODO: stack compression / deep slot fishing
          -- TODO: invariant: either stack too deep or all required slots are reachable

          -- TODO: top incorrect and not required in args: swap up a compatible slot
          -- TODO: invariant: the top is in place and all slots are reachable

          -- TODO: if there is any slot we need more of to populate args, dup it
          -- TODO: all required slots are present in required quantity

          -- TODO: swap up any reachable slot that is still out of position and not the same as head

          -- TODO: we only get here if there is a slot that is out of position and not reachable. last ditch compress the stack again
          -- TODO: need to avoid an infinite loop here

          -- otherwise: stack too deep :-(
          throw .StackTooDeep

--theorem shuffle_correct : ∀ (stack : Stack) (target : Target),
  --∃ (res : Stack), .ok res = shuffle stack target ∧ res
