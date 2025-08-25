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
      else ⟨hd :: rest.val, by
        simp ; apply And.intro
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

abbrev Stack := List Slot

def Stack.vars (s : Stack) : LSet Var :=
  let unwrap := λ s =>
    match s with
      | .Var v => some v
      | _ => none

  s |> List.filterMap unwrap |> LSet.ofList

--- Targets ---

-- A target is a specification of a desired shuffle outcome
structure Target where
  -- a concrete args section that must have a specific order and multiplicity
  args : Stack
  -- an abstract tail section that is a set of variables that must remain live for downstream ops
  liveOut : LSet Var

def Target.surplus (target : Target) (stack : Stack) (slot : Slot) : Prop :=
  let target_args_count := target.args.count slot
  let stack_head_count := stack |> List.take target.args.length |> List.count slot
  match slot with
  | .Var v => target_args_count < stack_head_count ∧ v ∈ target.liveOut
  | .Lit _ => target_args_count < stack_head_count
  | .Junk => True

instance (target : Target) (stack : Stack) (slot : Slot) : Decidable (target.surplus stack slot) := by
  unfold Target.surplus
  match slot with
  | .Var v => exact inferInstance
  | .Lit _ => exact inferInstance
  | .Junk => exact isTrue trivial

--- Stack Manipulation ---

inductive Op where
  -- swap0 is a noop, the others match the evm
  | Swap     : Fin 17 → Op
  -- dupn => evm dup(n + 1)
  | Dup      : Fin 16 → Op
  | Pop      : Op
  | Push     : Word → Op
  | MarkJunk : Fin 1024 → Op

inductive Err where
  | StackTooDeep : Err
  | StackTooShallow : Err

def Stack.apply (stack : Stack) : Op → Except Err Stack
  | .Swap idx =>
      if h : idx < stack.length
      then
        let s := stack.set 0 stack[idx]
        return s.set (idx) stack[0]
      else throw .StackTooShallow
  | .Dup idx =>
      if h : idx < stack.length
      then return (stack[idx] :: stack)
      else throw .StackTooShallow
  | .Pop =>
      if stack.length > 0
      then return stack.tail
      else throw .StackTooShallow
  | .Push v => return (.Lit v :: stack)
  | .MarkJunk idx =>
      if idx < stack.length
      then return stack.set idx .Junk
      else throw .StackTooShallow

-- apply theorems --

-- applying swap at the same idx twice is a noop
theorem apply_swap_inv (stack : Stack) (idx : Fin 17) (h : idx < stack.length) :
  stack.apply (.Swap idx) >>= (·.apply (.Swap idx)) = .ok stack := by
    simp_all [Stack.apply, Bind.bind, Except.bind, pure, Except.pure, List.length_set]
    ext i
    simp [List.getElem_set]
    split_ifs
    · simp_all
    · simp_all only [List.getElem?_set]
      split_ifs <;> simp_all

-- swap does not change the length of the stack
theorem apply_swap_length (stack : Stack) (idx : Fin 17) (h : idx < stack.length) :
  List.length <$> stack.apply (.Swap idx) = .ok stack.length := by
    simp_all [Stack.apply, pure, Except.pure, List.length_set]

-- swap switches the elem at idx with the elem at 0
theorem apply_swap_positions_switched (stack : Stack) (idx : Fin 17) (h : idx < stack.length) :
  ∃ (s' : Stack), stack.apply (.Swap idx) = .ok s' ∧ s'[0]? = some stack[idx] ∧ s'[idx]? = some stack[0] := by
  simp_all [Stack.apply, pure, Except.pure, List.length_set, List.getElem?_set]
  split_ifs <;> simp_all

-- dup grows stack size by 1
theorem apply_dup_grows_stack (stack : Stack) (idx : Fin 16) (h : idx < stack.length) :
  (stack.apply (.Dup idx) >>= (pure $ ·.length)) = .ok (stack.length + 1) := by
    simp_all [Stack.apply, Bind.bind, Except.bind, pure, Except.pure]

-- the stack head is the same as the element at idx after applying (dup idx)
theorem apply_dup_stack_top_eq_idx (stack : Stack) (idx : Fin 16) (h : idx < stack.length) :
  (stack.apply (.Dup idx) >>= (pure $ ·[0]?)) = .ok (stack[idx]?) := by
    simp_all [Stack.apply, Bind.bind, Except.bind, pure, Except.pure]

-- the tail of the new stack is the same as the starting stack after applying (dup idx)
theorem apply_dup_stack_tail_eq_prev (stack : Stack) (idx : Fin 16) (h : idx < stack.length) :
  (stack.apply (.Dup idx) >>= (pure $ ·.tail)) = .ok (stack) := by
    simp_all [Stack.apply, Bind.bind, Except.bind, pure, Except.pure]

-- the result of applying pop is the same as the tail of the input stack
theorem apply_pop_eq_prev_stack_tail (stack : Stack) (h : stack.length > 0) :
  stack.apply .Pop = .ok (stack.tail) := by
    simp_all [Stack.apply, pure, Except.pure]

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
      if h_top_is_surplus : target.surplus (stack.take 1) stack[0] then
        -- pop it
        let s' ← stack.apply .Pop
        -- TODO: recurse
        return s'
      else

        -- invariant: the top is either required in args or in tail or is junk
        let top := stack[0]
        -- if the top is junk and popping it fixes one or more positions in args
        if h_popping_junk_fixes_args : top = .Junk ∧ True then
          -- pop it
          let s' ← stack.apply .Pop
          -- TODO: recurse
          return s'

        return stack

--theorem shuffle_correct : ∀ (stack : Stack) (target : Target),
  --∃ (res : Stack), .ok res = shuffle stack target ∧ res
