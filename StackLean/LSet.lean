import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup
import Aesop

/-
 - An LSet is an alternative set definition built on top of a concrete list.
 - Unlike the Set and Finset definitions in Mathlib, this one has computable enumeration.
 -/

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
