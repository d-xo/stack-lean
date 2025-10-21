import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Nodup
import Aesop

/-
 - An LSet is an alternative set definition built on top of a concrete list.
 - Unlike the Set and Finset definitions in Mathlib, this one has computable enumeration.
 -/

def LSet (α : Type) := { l : List α // List.Nodup l }

@[simp]
def LSet.count (s : LSet α) : ℕ := s.val.length

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

def LSet.map {α β : Type} [DecidableEq β] (s : LSet α) (f : α → β) : LSet β := LSet.ofList (s.val.map f)

instance [DecidableEq α] : Union (LSet α) where
  union l r := LSet.ofList (l.val ++ r.val)

theorem lset_of_list_mem {α : Type} [DecidableEq α] (l : List α) (elem : α) :
    elem ∈ l ↔ elem ∈ LSet.ofList l
  := by
    apply Iff.intro
    · intro hmem
      induction l with
      | nil => simp_all
      | cons hd tl ih =>
        cases hmem with
        | head =>
          unfold LSet.ofList
          by_cases h : elem ∈ LSet.ofList tl
          · simp [h]
          · simp [h]
            exact List.Mem.head (LSet.ofList tl).val
        | tail a h =>
          simp [LSet.ofList]
          split_ifs with h'
          · exact (ih h)
          · unfold Membership.mem
            unfold instMembershipLSet
            simp
            apply Or.intro_right
            unfold Membership.mem
            unfold List.instMembership
            simp
            exact (ih h)
    · intro hmem
      unfold Membership.mem at hmem
      unfold instMembershipLSet at hmem
      simp at hmem
      unfold Membership.mem
      unfold List.instMembership
      simp
      induction l generalizing elem with
      | nil => exact hmem
      | cons hd tl ih =>
        simp_all [LSet.ofList]
        split_ifs at hmem with hm
        · exact List.Mem.tail hd (ih elem hmem)
        · unfold Membership.mem at hmem
          unfold List.instMembership at hmem
          simp at hmem
          cases hmem with
          | head =>
            exact List.Mem.head tl
          | tail e h =>
            exact List.Mem.tail hd (ih elem h)

theorem lset_of_list_not_mem {α : Type} [DecidableEq α] (l : List α) (elem : α) :
    elem ∉ l ↔ elem ∉ LSet.ofList l
  := by
    apply Iff.intro
    · intro hmem
      induction l with
      | nil => exact hmem
      | cons hd tl ih =>
        simp [LSet.ofList]
        split_ifs with h
        · exact ih (List.not_mem_of_not_mem_cons hmem)
        · obtain hnmem := ih (List.not_mem_of_not_mem_cons hmem)
          obtain hnhead : elem ≠ hd := List.ne_of_not_mem_cons hmem
          unfold Membership.mem
          unfold instMembershipLSet
          simp
          exact ⟨hnhead, hnmem⟩
    · intro hmem
      induction l with
      | nil => exact hmem
      | cons hd tl ih =>
        simp; apply And.intro
        · simp_all [LSet.ofList]
          split_ifs at hmem with h
          · grind only
          · intro heq
            subst heq
            unfold Membership.mem at hmem
            unfold instMembershipLSet at hmem
            simp at hmem
        · simp_all [LSet.ofList]
          split_ifs at hmem with h
          · exact ih hmem
          · unfold Membership.mem at hmem
            unfold instMembershipLSet at hmem
            simp at hmem
            obtain ⟨hl, hr⟩ := hmem
            exact ih hr


