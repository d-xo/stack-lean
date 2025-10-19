import Mathlib.Data.Nat.Basic

def List.swap
  {α : Type u} (xs : List α) (i j : ℕ)
  (hi : i < xs.length := by get_elem_tactic)
  (hj : j < xs.length := by get_elem_tactic)
  := (xs.set i xs[j]).set j xs[i]
