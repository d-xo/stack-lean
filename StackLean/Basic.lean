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
  deriving BEq, Hashable, DecidableEq

abbrev Stack := List Slot

structure Target where
  args : Stack
  tail : Multiset Slot

inductive Op where
  | Swap     : Fin 16 → Op
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
        return s.set idx stack[0]
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

theorem apply_swap_inv (stack : Stack) (idx : Fin 16) (h : idx < stack.length) :
  stack.apply (.Swap idx) >>= (·.apply (.Swap idx)) = .ok stack := by
    simp_all [Stack.apply, pure, Except.pure]
    sorry



--def shuffle (stack : Stack) (target : Target) : Except Err Stack := do
  --let (head, tail) := stack.splitAt target.args.length
  ---- check if the current head matches the target head
  --if head == target.args then
    ---- check if any of the args are also required in the tail and not there yet
    --let missing := (target.tail - (Multiset.ofList tail)).toFinset
    --for slot in missing do
      --match head.findIdx? (· == slot) with
      --| .none => continue
      --| .some idx =>
        --if h : idx < 16 then
          --return path ++ [Op.Dup ⟨idx, h⟩]
        --else
          --throw "Can't dup past 16..."
    --return path
  --return path
