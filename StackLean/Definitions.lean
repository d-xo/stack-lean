import Init.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Aesop

import StackLean.LSet
import StackLean.Util

--- Basic Types ---

abbrev Word := Fin (2 ^ 256)

--- Stack Slots ---

-- A var is a newtype around a Nat
abbrev Var := ℕ

-- In addition to variables, slots can contain literals and junk elems
inductive Slot where
  | Var : Var → Slot
  | Lit : Word → Slot
  | Junk : Slot
  deriving DecidableEq, Repr

instance : LawfulBEq Var := inferInstance
instance : LawfulBEq Slot := inferInstance

def slotToVar : Slot → Option Var
  | .Var v => some v
  | _ => none

def Slot.isJunk : Slot → Prop
  | .Junk => True
  | _ => False

instance (s : Slot) : Decidable (s.isJunk) :=
  match s with
  | .Junk => isTrue (by simp [Slot.isJunk])
  | .Lit _ => isFalse (by simp [Slot.isJunk])
  | .Var _ => isFalse (by simp [Slot.isJunk])

--- Stacks ---

abbrev Stack := List Slot

def List.vars (stack : Stack) : LSet Var := stack |> List.filterMap slotToVar |> LSet.ofList

-- gives back the set of all non junk elements
def List.elems (stack : Stack) : LSet Slot :=
  stack |> List.dedup |> List.filter (λ s => ¬s.isJunk) |> LSet.ofList

theorem list_elems_mem (s : Slot) (stack : Stack) (hmem : s ∈ stack) (hnj : ¬s.isJunk) : s ∈ stack.elems := by
  simp only [List.elems]
  have h1 : s ∈ List.dedup stack := List.mem_dedup.mpr hmem
  have h2 : s ∈ List.filter (fun s => decide ¬s.isJunk) (List.dedup stack) := by
    apply List.mem_filter_of_mem
    · exact h1
    · cases s with
      | Junk => contradiction
      | Var _ => simp [Slot.isJunk]
      | Lit _ => simp [Slot.isJunk]

  exact (lset_of_list_mem _ _).mp h2

theorem list_elems_mem_junk (s : Slot) (stack : Stack) (hmem : s ∈ stack) (hnj : s.isJunk) : s ∉ stack.elems := by
  simp only [List.elems]
  have h1 : s ∈ List.dedup stack := List.mem_dedup.mpr hmem
  have h2 : s ∉  List.filter (fun s => decide ¬s.isJunk) (List.dedup stack) := by
    grind only [List.mem_filter, =_ List.contains_iff_mem]
  exact (lset_of_list_not_mem _ _).mp h2

theorem list_elems_not_mem (s : Slot) (stack : Stack) (hmem : s ∉ stack) : s ∉ stack.elems := by
  simp only [List.elems]
  have : s ∉ List.dedup stack := by rw [List.mem_dedup]; exact hmem
  have h : s ∉ List.filter (fun s => decide ¬s.isJunk) (List.dedup stack) := by
    intro h; have : s ∈ List.dedup stack := List.mem_filter.mp h |>.1
    contradiction
  exact (lset_of_list_not_mem _ _).mp h

--- Targets ---

-- A target is a specification of a desired shuffle outcome
structure Target where
  -- a concrete args section that must have a specific order and multiplicity
  args : Stack
  -- an abstract tail section that is a set of variables that must remain live for downstream ops
  liveOut : LSet Var
  -- the size of the target stack
  size : { n : ℕ // n ≥ args.length + liveOut.count }

instance : Membership Slot Target where
  mem (target : Target) (s : Slot) := match s with
    | .Var v => s ∈ target.args ∨ v ∈ target.liveOut
    | .Lit _ => s ∈ target.args
    | .Junk => s ∈ target.args

instance (target : Target) (s : Slot) : Decidable (s ∈ target) := match s with
  | .Var v => inferInstanceAs (Decidable (.Var v ∈ target.args ∨ v ∈ target.liveOut))
  | .Lit a => inferInstanceAs (Decidable (.Lit a ∈ target.args))
  | .Junk => inferInstanceAs (Decidable (.Junk ∈ target.args))

def Target.vars (target : Target) : LSet Var := target.args.vars ∪ target.liveOut

-- gives back the set of all non junk elements
def Target.elems (target : Target) : LSet Slot := target.args.elems ∪ target.liveOut.map (.Var)

theorem target_elems_mem (s : Slot) (target : Target) (hmem : s ∈ target) (hnj : ¬s.isJunk) : s ∈ target.elems := by
  simp only [Target.elems]
  rw [lset_union_or_mem]
  cases s with
  | Junk => contradiction
  | Var v =>
    have h1 : (.Var v) ∈ target.args ∨ v ∈ target.liveOut := by simpa using hmem
    cases h1 with
    | inl h_args =>
      have h2 : (.Var v) ∈ target.args.elems := list_elems_mem (.Var v) target.args h_args hnj
      exact Or.inl h2
    | inr h_live =>
      have h3 : (Slot.Var v) ∈ target.liveOut.map (.Var) := by
        simp only [LSet.map]
        have h4 : v ∈ target.liveOut.val := by
          unfold Membership.mem
          unfold List.instMembership
          simp
          exact h_live
        have h5 : Slot.Var v ∈ List.map Slot.Var target.liveOut.val := by
          apply List.mem_map_of_mem
          exact h4
        have h6 : Slot.Var v ∈ LSet.ofList (List.map Slot.Var target.liveOut.val) := by
          rw [←lset_of_list_mem _ _]
          exact h5
        exact h6
      exact Or.inr h3
  | Lit w =>
    have h1 : (.Lit w) ∈ target.args := by simpa using hmem
    have h2 : (.Lit w) ∈ target.args.elems := list_elems_mem (.Lit w) target.args h1 hnj
    exact Or.inl h2

theorem target_elems_mem_junk (s : Slot) (target : Target) (hmem : s ∈ target) (hnj : s.isJunk) : s ∉ target.elems := by
  cases s with
  | Junk =>
    simp only [Target.elems]
    have h1 : Slot.Junk ∈ target.args := by simpa using hmem
    have : Slot.Junk ∉ target.args.elems := list_elems_mem_junk Slot.Junk target.args h1 (by simp [Slot.isJunk])
    intro h
    have : Slot.Junk ∈ target.args.elems ∨ Slot.Junk ∈ target.liveOut.map (fun v => Slot.Var v) := by
      rw [lset_union_or_mem] at h; simpa using h
    cases this with
    | inl h_args => contradiction
    | inr h_live =>
      have h2 : Slot.Junk ∈ List.map (fun v => Slot.Var v) target.liveOut.val := by
        rw [lset_of_list_mem]
        simpa using h_live
      obtain ⟨_, _, hv2⟩ := List.mem_map.mp h2
      cases hv2
  | Var v => contradiction
  | Lit w => contradiction

theorem target_elems_not_mem (s : Slot) (target : Target) (hmem : s ∉ target) : s ∉ target.elems := by
  simp only [Target.elems]
  rw [lset_union_or_mem]
  cases s with
  | Junk =>
    intro h
    unfold Membership.mem at hmem
    unfold instMembershipSlotTarget at hmem
    simp at hmem
    cases h with
    | inl h' =>
      apply list_elems_not_mem (.Junk) target.args hmem
      exact h'
    | inr h' =>
      exfalso
      simp [LSet.map] at h'
      rw [←lset_of_list_mem] at h'
      obtain ⟨v, hv1, hv2⟩ := List.mem_map.mp h'
      cases hv2
  | Lit w =>
    intro h
    unfold Membership.mem at hmem
    unfold instMembershipSlotTarget at hmem
    simp at hmem
    cases h with
    | inl h' =>
      apply list_elems_not_mem (.Lit w) target.args hmem
      exact h'
    | inr h' =>
      exfalso
      simp [LSet.map] at h'
      rw [←lset_of_list_mem] at h'
      obtain ⟨v, hv1, hv2⟩ := List.mem_map.mp h'
      cases hv2
  | Var v =>
    intro h
    unfold Membership.mem at hmem
    unfold instMembershipSlotTarget at hmem
    simp at hmem
    cases h with
    | inl h' =>
      apply list_elems_not_mem (.Var v) target.args hmem.left
      exact h'
    | inr h' =>
      exfalso
      simp [LSet.map] at h'
      rw [←lset_of_list_mem] at h'
      obtain ⟨v, hv1, hv2⟩ := List.mem_map.mp h'
      cases hv2
      obtain ⟨hl, hr⟩ := hmem
      contradiction


@[simp]
abbrev Target.tail_length (target : Target) := target.size - target.args.length
--- Stack Args ---

@[simp, reducible]
def Stack.args (stack : Stack) (target : Target) : Stack :=
  if stack.length > target.size
  then
    stack
      -- drop the excess
      |> List.drop (stack.length - target.size)
      -- take the args
      |> List.take target.args.length
  else
    -- take whatever stack region we have above the tail
    stack.take (stack.length - target.tail_length)

@[simp]
abbrev example_target (args_sz : ℕ) (total_sz : ℕ) (hsz : total_sz ≥ args_sz := by omega) : Target
  := ⟨List.replicate args_sz (.Lit 1), LSet.ofList [], ⟨total_sz, by simp [LSet.ofList]; grind⟩⟩

example : Stack.args [.Lit 3, .Lit 4, .Lit 5] (example_target 2 4) = [.Lit 3]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 3) = [.Lit 3, .Lit 4]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 4) = [.Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 2) = [.Lit 4, .Lit 5]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 5) = [.Lit 1, .Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 6) = [.Lit 1]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 7 10) = [.Lit 1, .Lit 2]
  := by simp_all [Stack.args]

example : Stack.args [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 10) = []
  := by simp_all [Stack.args]

@[simp]
theorem args_le_target_args (stack : Stack) (target : Target)
  : (stack.args target).length ≤ target.args.length := by
    simp_all [Stack.args]
    grind only [= List.length_drop, = List.length_take, = Nat.min_def, cases Or]

@[simp]
theorem args_le_stack_length (stack : Stack) (target : Target)
  : (stack.args target).length ≤ stack.length := by
    simp_all [Stack.args]
    grind only [= List.length_drop, = List.length_take, = Nat.min_def, cases Or]

@[simp]
theorem stack_args_sublist_stack (stack : Stack) (target : Target)
  : List.Sublist (stack.args target) stack := by
    simp_all [Stack.args]
    split_ifs with hsz
    · apply List.Sublist.trans (List.take_sublist _ _) (List.drop_sublist _ _)
    · grind only [List.take_sublist, usr List.Sublist.length_le, → List.Sublist.subset]

-- if we prepend the target args any base with length ≤ the tail length, and
-- then take the args of that stack relative to the target, the result is the target.args
theorem args_concat_base_leq
  (base : Stack) (target : Target) (hsz : base.length ≤ target.tail_length)
    : let input := target.args ++ base
      input.args target = target.args.take (input.length - target.tail_length)
  := by
    simp_all [Stack.args]
    split_ifs
    · grind
    · simp_all

-- if we prepend the target args any base with length = the tail length, and
-- then prepend any stack to that, the args of the result relative to the target is the target.args
theorem args_concat_top_base_eq
  (top : Stack) (base : Stack) (target : Target) (hsz : base.length = target.tail_length)
    : let input := top ++ target.args ++ base
      input.args target = target.args
  := by
    simp_all [Stack.args]
    split_ifs
    · have :
        (top.length +
          (target.args.length + (↑target.size - target.args.length))
        - ↑target.size) = top.length := by grind
      simp_all
    · have : top.length = 0 := by omega
      simp_all

--- Stack Tail ---

@[simp, reducible]
def Stack.tail_region (stack : Stack) (target : Target) : Stack :=
    if stack.length > target.size
    then
      -- drop the excess and the args
      stack.drop ((stack.length - target.size) + target.args.length)
    else
      -- drop whatever stack region we have above the tail
      let tail_length := target.size - target.args.length
      stack.drop (stack.length - tail_length)

example : Stack.tail_region [.Lit 3, .Lit 4, .Lit 5] (example_target 2 4) = [.Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 3) = [.Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 4) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 2) = []
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 5) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 2 6) = [.Lit 2, .Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 7 10) = [.Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

example : Stack.tail_region [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5] (example_target 1 10) = [.Lit 1, .Lit 2, .Lit 3, .Lit 4, .Lit 5]
  := by simp_all [Stack.tail_region]

theorem stack_tail_le_target_tail_length (stack : Stack) (target : Target) : (stack.tail_region target).length ≤ target.tail_length := by
  simp_all [Stack.tail_region]
  split_ifs <;> grind only [= List.length_drop, cases Or]

theorem stack_tail_eq_stack_length_leq_tail_length
  (stack : Stack) (target : Target)
  (hlen : stack.length ≤ target.tail_length)
    : stack.tail_region target = stack := by
  simp_all [Stack.tail_region]
  intro hsz
  grind

theorem stack_tail_eq_stack_length_gt_tail_length
  (stack : Stack) (target : Target)
  (hlen : stack.length > target.tail_length)
    : stack.tail_region target = stack.drop (stack.length - target.tail_length) := by
  simp_all [Stack.tail_region]
  intro hsz
  grind

--- Stack Stats ---

def Stack.total_count (stack : Stack) (slot : Slot) : ℕ := stack.count slot

def Target.min_count (target : Target) (slot : Slot) : ℕ :=
  match slot with
    | .Var v => target.args.count slot + (if v ∈ target.liveOut then 1 else 0)
    | .Lit _ => target.args.count slot
    | .Junk => 0

--- Traces ---

-- A Trace is evidence of a valid sequence of operations transforming one stack into another
-- It relates an input stack to the set of all stacks reachable from it
inductive Trace : Stack → Stack → Prop where
  | Lit
    : (s : Stack)
    → Trace s s
  | Swap
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev.swap 0 idx)
  | Dup
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → (hlo : 1 ≤ idx)
    → (hhi : idx < 17)
    → Trace start prev
    → Trace start (prev[idx - 1] :: prev)
  | Pop
    : (hlen : 0 < prev.length)
    → Trace start prev
    → Trace start prev.tail
  | Push
    : (w : Word)
    → Trace start prev
    → Trace start (.Lit w :: prev)
  | MarkJunk
    : (idx : ℕ)
    → (hlen : idx < prev.length)
    → Trace start prev
    → Trace start (prev.set idx .Junk)

-- apply theorems --

-- applying dup to any trace grows the length of the result by one
theorem dup_grows_stack_by_one
  (start : Stack) (stack : Stack) (trace : Trace start stack)
  (idx : ℕ) (hlen : idx < stack.length) (hlo : 1 ≤ idx) (hhi : idx < 17) :
    let result : Stack := _
    let _ : Trace start result := trace |> .Dup idx hlen hlo hhi
    result.length = stack.length + 1
  := by simp


-- applying swap at the same idx twice to any stack is a noop
theorem apply_swap_inv
  (start : Stack) (stack : Stack) (trace : Trace start stack)
  (idx : ℕ) (hlen : idx < stack.length) (hlo : 1 ≤ idx) (hhi : idx < 17) :
    let result : Stack := _
    let _ : Trace start result
      := trace
      |> .Swap idx hlen hlo hhi
      |> .Swap idx (by simp [List.swap]; omega) (by omega) (by omega)
    stack = result
  := by
    simp_all [List.swap, List.getElem_set]
    split_ifs
    · simp_all
    · ext i; grind
