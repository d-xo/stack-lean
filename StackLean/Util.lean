import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

def List.swap
  {α : Type u} (xs : List α) (i j : ℕ)
  (hi : i < xs.length := by get_elem_tactic)
  (hj : j < xs.length := by get_elem_tactic)
  := (xs.set i xs[j]).set j xs[i]

def List.findFinIdxWithProof? {α : Type} (p : α → Bool) (xs : List α)
  : Option { idx : Fin xs.length // p (xs.get idx) = true } :=
  match xs with
  | [] => none
  | x :: xs' =>
    if h_pred : p x then
      let idx : Fin (x :: xs').length := ⟨0, by simp⟩
      have h_get : (x :: xs').get idx = x := by
        simp [idx]
      some ⟨idx, by rw [h_get]; exact h_pred⟩
    else
      match findFinIdxWithProof? p xs' with
      | none => none
      | some ⟨idx', h_pred'⟩ =>
        have h_idx : idx'.val + 1 < (x :: xs').length := by
          have h1 : idx'.val < xs'.length := idx'.isLt
          simp at h1 ⊢
        let idx : Fin (x :: xs').length := ⟨idx'.val + 1, h_idx⟩
        have h_get : (x :: xs').get idx = xs'.get idx' := by
          simp [idx, List.get_eq_getElem]
        some ⟨idx, by rw [h_get]; exact h_pred'⟩

def List.findLastFinIdxWithProof? {α : Type} (p : α → Bool) (xs : List α)
  : Option { idx : Fin (xs.length) // p (xs.get idx) = true } :=
  match xs.reverse.findFinIdxWithProof? p with
  | none => none
  | some ⟨i, h⟩ =>
    -- we have an element thereforre it's non zero
    have : NeZero xs.length := by
      apply NeZero.mk
      intro h
      have h_length : xs.reverse.length = xs.length := List.length_reverse
      have h_nonempty : xs.reverse.length > 0 := by
        rw [h_length]
        have : i.val < xs.length := by
          rw [← h_length]
          exact i.2
        omega
      rw [h_length, h] at h_nonempty
      omega
    have h_pos : 0 < xs.length := by
      have h_length : xs.reverse.length = xs.length := List.length_reverse
      rw [← h_length]
      have : 0 < xs.reverse.length := by
        have h_bound : (i : ℕ) < xs.reverse.length := i.2
        omega
      assumption
    let len : Fin xs.length := ⟨xs.length - 1, by omega⟩
    let idx : Fin xs.length := len - (Fin.cast List.length_reverse i)
    .some ⟨idx, (by
      have h_reverse_property : xs.reverse.get i = xs.get ⟨xs.length - 1 - (i : ℕ), by omega⟩ :=
        List.get_reverse' xs i (by omega)
      have h_idx_equality : idx = ⟨xs.length - 1 - (i : ℕ), by omega⟩ := by
        ext
        simp [idx, len]
        show (⟨xs.length - 1, _⟩ - Fin.cast List.length_reverse i).val = xs.length - 1 - i.val
        rw [Fin.sub_def]
        simp
        have h_bound : ↑i < xs.length := by
          have : ↑i < xs.reverse.length := i.2
          have h_length : xs.reverse.length = xs.length := List.length_reverse
          omega
        by_cases h_zero : (i : ℕ) = 0
        · rw [h_zero]
          simp
        · have h_pos : 0 < (i : ℕ) := by omega
          have h_decomp : xs.length - ↑i + (xs.length - 1) = xs.length + (xs.length - ↑i - 1) := by omega
          rw [h_decomp]
          rw [Nat.add_mod]
          simp
          have h_lt : xs.length - ↑i - 1 < xs.length := by omega
          rw [Nat.mod_eq_of_lt h_lt]
          omega

      have h_get_equality : xs.get idx = xs.get ⟨xs.length - 1 - (i : ℕ), by omega⟩ := by
        rw [h_idx_equality]

      -- We need to show p xs[idx] = true
      -- But we have h : p (xs.reverse.get i) = true
      -- and we've shown that xs.get idx = xs.reverse.get i
      
      -- So we can use the equality directly
      rw [h_get_equality]
      rw [← h_reverse_property]
      exact h
    )⟩

theorem List.find_idx_proof_mem (α : Type) (x : α) (xs : List α) (p : α → Bool) (hp : p x = true) (hmem : x ∈ xs) :
  ∃ (idx : Fin xs.length) (hpi : p (xs.get idx) = true), xs.findFinIdxWithProof? p = some ⟨idx,  hpi⟩ := by
    induction hmem with
    | head => simp [List.findFinIdxWithProof?, hp]
    | tail y ys ih =>
      simp [List.findFinIdxWithProof?]
      split <;> simp_all
      · obtain ⟨i, ⟨h, j⟩⟩ := ih
        simp_all

theorem List.find_last_idx_proof_mem (α : Type) (x : α) (xs : List α) (p : α → Bool) (hp : p x = true) (hmem : x ∈ xs) :
  ∃ (idx : Fin xs.length) (hpi : p (xs.get idx) = true), xs.findLastFinIdxWithProof? p = some ⟨idx,  hpi⟩ := by
    -- Since x ∈ xs, there must be some occurrence of x in xs
    -- The last occurrence of x in xs corresponds to the first occurrence of x in xs.reverse

    -- First, find the first occurrence of x in xs.reverse
    have h_reverse_mem : x ∈ xs.reverse := by
      rw [List.mem_reverse]
      exact hmem

    -- Use the existing theorem for findFinIdxWithProof? on the reversed list
    have h_find_reverse : ∃ (idx_rev : Fin xs.reverse.length) (hpi_rev : p (xs.reverse.get idx_rev) = true),
        xs.reverse.findFinIdxWithProof? p = some ⟨idx_rev, hpi_rev⟩ := by
      exact List.find_idx_proof_mem α x xs.reverse p hp h_reverse_mem

    -- Now we need to convert this to the original list
    rcases h_find_reverse with ⟨idx_rev, hpi_rev, h_find⟩

    -- The findLastFinIdxWithProof? function should return the corresponding index in the original list
    -- It does this by finding idx_rev in the reversed list and converting it back

    -- Show that findLastFinIdxWithProof? returns some result
    simp [List.findLastFinIdxWithProof?, h_find]

    -- We need to construct the index in the original list
    -- The conversion is: idx = xs.length - 1 - idx_rev
    have h_pos : 0 < xs.length := by
      -- Since x ∈ xs, the list is non-empty
      cases hmem with
      | head => simp
      | tail _ _ => simp

    let len : Fin xs.length := ⟨xs.length - 1, by omega⟩
    let idx : Fin xs.length := len - (Fin.cast List.length_reverse idx_rev)

    -- We need to show that p (xs.get idx) = true
    -- This follows from the property we proved in findLastFinIdxWithProof?
    have h_get_eq : xs.get idx = xs.reverse.get idx_rev := by
      -- This follows from the index conversion property:
      -- xs.get idx = xs.get (xs.length - 1 - idx_rev) = xs.reverse.get idx_rev

      -- First, show that idx corresponds to xs.length - 1 - idx_rev
      have h_idx_eq : idx = ⟨xs.length - 1 - (idx_rev : ℕ), by omega⟩ := by
        ext
        simp [idx, len]
        show (⟨xs.length - 1, _⟩ - Fin.cast List.length_reverse idx_rev).val = xs.length - 1 - (idx_rev : ℕ)
        rw [Fin.sub_def]
        simp
        have h_bound : (idx_rev : ℕ) < xs.length := by
          have : (idx_rev : ℕ) < xs.reverse.length := idx_rev.2
          have h_length : xs.reverse.length = xs.length := List.length_reverse
          omega

        -- Use the same modular arithmetic proof as in findLastFinIdxWithProof?
        by_cases h_zero : (idx_rev : ℕ) = 0
        · rw [h_zero]
          simp
        · have h_pos : 0 < (idx_rev : ℕ) := by omega
          have h_decomp : xs.length - (idx_rev : ℕ) + (xs.length - 1) = xs.length + (xs.length - (idx_rev : ℕ) - 1) := by omega
          rw [h_decomp]
          rw [Nat.add_mod]
          simp
          have h_lt : xs.length - (idx_rev : ℕ) - 1 < xs.length := by omega
          rw [Nat.mod_eq_of_lt h_lt]
          omega

      -- Now use the reverse property
      have h_reverse_prop : xs.reverse.get idx_rev = xs.get ⟨xs.length - 1 - (idx_rev : ℕ), by omega⟩ :=
        List.get_reverse' xs idx_rev (by omega)

      rw [h_idx_eq]
      rw [← h_reverse_prop]

    have hpi : p (xs.get idx) = true := by
      rw [h_get_eq]
      exact hpi_rev

    -- The goal is p xs[↑(⟨xs.length - 1, ⋯⟩ - Fin.cast ⋯ idx_rev)] = true
    -- We already have hpi : p (xs.get idx) = true
    
    -- Since idx is defined as len - Fin.cast List.length_reverse idx_rev where len = ⟨xs.length - 1, ⋯⟩
    -- the expression xs[↑(⟨xs.length - 1, ⋯⟩ - Fin.cast ⋯ idx_rev)] should equal xs.get idx
    
    -- We can prove this by showing the indices are equal
    have h_idx_eq : ↑(⟨xs.length - 1, by omega⟩ - Fin.cast (by rw [List.length_reverse]) idx_rev) = ↑idx := by
      simp [idx, Fin.sub_def]
      have h_len_val : ↑len = xs.length - 1 := rfl
      simp [h_len_val]
    
    rw [h_idx_eq]
    exact hpi
