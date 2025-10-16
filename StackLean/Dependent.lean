import Mathlib.Order.Interval.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
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

inductive Stack : List Slot → Type where
  | Lit : (stk : List Slot) → Stack stk
  | Push : Stack s → (lit: Word) → Stack ((.Lit lit) :: s)
  | Pop : Stack (top :: rest) → Stack rest
  | MarkJunk : Stack s → (ix : Fin s.length) → Stack (s.set ix .Junk)
  | Swap1
    : Stack (s00 :: s01 :: rest)
    → Stack (s01 :: s00 :: rest)
  | Swap2
    : Stack (s00 :: s01 :: s02 :: rest)
    → Stack (s02 :: s01 :: s00 :: rest)
  | Swap3
    : Stack (s00 :: s01 :: s02 :: s03 :: rest)
    → Stack (s03 :: s01 :: s02 :: s00 :: rest)
  | Swap4
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: rest)
    → Stack (s04 :: s01 :: s02 :: s03 :: s00 :: rest)
  | Swap5
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: rest)
    → Stack (s05 :: s01 :: s02 :: s03 :: s04 :: s00 :: rest)
  | Swap6
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: rest)
    → Stack (s06 :: s01 :: s02 :: s03 :: s04 :: s05 :: s00 :: rest)
  | Swap7
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: rest)
    → Stack (s07 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s00 :: rest)
  | Swap8
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: rest)
    → Stack (s08 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s00 :: rest)
  | Swap9
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: rest)
    → Stack (s09 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s00 :: rest)
  | Swap10
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: rest)
    → Stack (s10 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s00 :: rest)
  | Swap11
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: rest)
    → Stack (s11 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s00 :: rest)
  | Swap12
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: rest)
    → Stack (s12 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s00 :: rest)
  | Swap13
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: rest)
    → Stack (s13 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s00 :: rest)
  | Swap14
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: rest)
    → Stack (s14 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s00 :: rest)
  | Swap15
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s15 :: rest)
    → Stack (s15 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s00 :: rest)
  | Swap16
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s15 :: s16 :: rest)
    → Stack (s16 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s15 :: s00 :: rest)
  | Dup1
    : Stack (s00 :: rest)
    → Stack (s00 :: s00 :: rest)
  | Dup2
    : Stack (s00 :: s01 :: rest)
    → Stack (s01 :: s00 :: s01 :: rest)
  | Dup3
    : Stack (s00 :: s01 :: s02 :: rest)
    → Stack (s02 :: s00 :: s01 :: s02 :: rest)
  | Dup4
    : Stack (s00 :: s01 :: s02 :: s03 :: rest)
    → Stack (s03 :: s00 :: s01 :: s02 :: s03 :: rest)
  | Dup5
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: rest)
    → Stack (s04 :: s00 :: s01 :: s02 :: s03 :: s04 :: rest)
  | Dup6
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: rest)
    → Stack (s05 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: rest)
  | Dup7
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: rest)
    → Stack (s06 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: rest)
  | Dup8
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: rest)
    → Stack (s07 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: rest)
  | Dup9
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: rest)
    → Stack (s08 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: rest)
  | Dup10
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: rest)
    → Stack (s09 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: rest)
  | Dup11
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: rest)
    → Stack (s10 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: rest)
  | Dup12
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: rest)
    → Stack (s11 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: rest)
  | Dup13
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: rest)
    → Stack (s12 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: rest)
  | Dup14
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: rest)
    → Stack (s13 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: rest)
  | Dup15
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: rest)
    → Stack (s14 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: rest)
  | Dup16
    : Stack (s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s15 :: rest)
    → Stack (s15 :: s00 :: s01 :: s02 :: s03 :: s04 :: s05 :: s06 :: s07 :: s08 :: s09 :: s10 :: s11 :: s12 :: s13 :: s14 :: s15 :: rest)


syntax "#Swap" num : term

macro_rules
  | `(#Swap $n:num) => return Lean.mkIdent (String.toName ((Lean.Name.toString `Stack.Swap).append (Nat.repr (Lean.TSyntax.getNat n))))


abbrev FinIco (lo hi : Nat) := { val : Nat // lo ≤ val ∧ val < hi }

syntax "#f" num : term

macro_rules
  | `(#f $n:num) => `(⟨$n, by omega⟩)

inductive Stack' : Vector Slot sz → Type where
  | Lit : (stk : Vector Slot sz) → Stack' stk
  | Swap
    : (idx : FinIco 1 (min 17 (.succ size)))
    → Stack' (elems : Vector Slot (.succ size))
    → (hlo : 0 < idx.val := by linarith)
    → (htop : idx < elems.size := by linarith)
    → Stack' (elems.swap 0 idx)

def s' := Stack'.Lit #v[.Lit 0, .Lit 1]
       |> (Stack'.Swap (#f 1))
       --|> (Stack'.swap (#f 1))
