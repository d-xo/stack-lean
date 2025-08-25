import Lean.Data.PersistentHashMap
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Finset.Basic
import Aesop

abbrev Word := Fin (2 ^ 256)

inductive Slot where
  | Var : Nat → Slot
  | Lit : Word → Slot
  | Junk : Slot
  deriving BEq, Hashable, Hashable, DecidableEq

abbrev Stack := List Slot

structure Target where
  args : Stack
  -- TODO: make this a Set
  tail : Multiset Slot

inductive Ty where
  | Int : Ty
  | Bool : Ty

inductive Op where
  -- swap0 is a noop, the others match the evm
  | Swap     : Fin 17 → Op
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

-- shuffle --

-- TODO: using Multiset is nice but idk how to make it computable
-- TODO: target can only be reached from stack if the variable set of target ⊆ the variable set of stack
noncomputable def shuffle (stack : Stack) (target : Target) : Except Err Stack := do
  if h_stack_empty : stack = [] then
    throw .StackTooShallow
  else

    let head := stack.take target.args.length
    let tail := stack.drop target.args.length

    -- check if the current head matches the target head
    if hargs : head = target.args then
      -- check if any of the args are also required in the tail and not there yet
      -- TODO: I'm probably handling junk wrong here
      let missing := (target.tail - (Multiset.ofList tail)).toFinset.toList
      for slot in missing do
        match head.findIdx? (· == slot) with
        | .none => continue
        -- dup if that is the case (or dup deep slot if required)
        -- TODO: what does dup deep slot if required mean??
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

      let top := stack[0]
      let top_is_surplus_in_args := top ∈ (Multiset.ofList head - target.args)
      let top_is_surplus_in_tail := top ∈ (Multiset.ofList tail - target.tail)

      -- if the top can be popped (args and tail have enough of it without it, it’s not junk)
      if h_top_is_surplus : top_is_surplus_in_args ∧ top_is_surplus_in_tail ∧ top ≠ .Junk then
        -- pop it
        let s' ← stack.apply .Pop
        -- TODO: recurse
        return s'
      else

        -- invariant: the top is either required in args or in tail or is junk
        -- TODO

        -- if the top is junk and popping it fixes one or more positions in args
        if h_popping_junk_fixes_args : top = .Junk ∧ True then
          -- pop it
          let s' ← stack.apply .Pop
          -- TODO: recurse
          return s'

        return stack

theorem shuffle_correct : ∀ (stack : Stack) (target : Target),
  ∃ (res : Stack), .ok res = shuffle stack target ∧ res
