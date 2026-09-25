import Crown.Orders
import Crown.Words
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.SplitIfs

/-!
# The explicit five-gap word

The alphabet is the disjoint union of the paired part `Fin k × Bool` and
the other vertex part `B`.  Boolean `false` labels x and `true` labels y.
The definitions below are literally the words W_i, D_i and their concatenation
from equations (2.3)--(2.4) of the Colbrook–Drysdale manuscript, with zero-based
indices. The construction adapts the method of Mozhui and Krishna, Section 2,
*On the conjecture of the representation number of bipartite graphs*
(arXiv:2506.01057v1), as developed in that manuscript.
-/

namespace Crown.Blocks

open scoped BigOperators

variable {k : ℕ} {B : Type*} [DecidableEq B]

abbrev Alphabet (k : ℕ) (B : Type*) := Sum (Fin k × Bool) B

-- Use the equality test chosen by `Crown.Uniform`, including on the sum type.
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def x (i : Fin k) : Alphabet k B := Sum.inl (i, false)
def y (i : Fin k) : Alphabet k B := Sum.inl (i, true)

def gap (rank : B → Fin 5) (π : List B) (j : Fin 5) : List (Alphabet k B) :=
  (π.filter fun b => rank b = j).map Sum.inr

def block (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) (i : Fin k) :
    List (Alphabet k B) :=
  gap (fun b => r b i) (π i) 0 ++ [x i] ++
  gap (fun b => r b i) (π i) 1 ++ [y i] ++
  gap (fun b => r b i) (π i) 2 ++ [x i] ++
  gap (fun b => r b i) (π i) 3 ++ [y i] ++
  gap (fun b => r b i) (π i) 4

def retained (i : Fin k) : List (Fin k) :=
  (List.finRange k).filter fun j => j ≠ i ∧ j ≠ finRotate k i

def separator (i : Fin k) : List (Alphabet k B) :=
  (retained i).map y ++ (retained i).map x

def word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) :
    List (Alphabet k B) :=
  (List.finRange k).flatMap fun i => block r π i ++ separator i

theorem count_gap_left (rank : B → Fin 5) (π : List B) (j : Fin 5)
    (a : Fin k × Bool) : (gap rank π j).count (Sum.inl a) = 0 := by
  simp [gap, List.count_eq_zero]

theorem count_gap_right (rank : B → Fin 5) (π : List B) (j : Fin 5) (b : B) :
    (gap rank π j : List (Alphabet k B)).count (Sum.inr b) =
      if rank b = j then π.count b else 0 := by
  rw [gap, List.count_map_of_injective _ Sum.inr Sum.inr_injective]
  by_cases h : rank b = j
  · simp [h]
  · simp [h, List.count_eq_zero]

theorem count_block_left (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) :
    (block r π i).count (Sum.inl (j, side)) = if j = i then 2 else 0 := by
  simp only [block, List.count_append, count_gap_left]
  by_cases h : j = i
  · subst j
    cases side <;> simp [x, y]
  · cases side <;> simp [x, y, h, Ne.symm h]

theorem count_block_right (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (b : B) : (block r π i).count (Sum.inr b) = (π i).count b := by
  have hb : r b i = 0 ∨ r b i = 1 ∨ r b i = 2 ∨ r b i = 3 ∨ r b i = 4 := by
    have hv := (r b i).isLt
    simp only [Fin.ext_iff]
    omega
  rcases hb with hb | hb | hb | hb | hb <;>
    simp [block, x, y, count_gap_right, hb]

theorem count_side_list (is : List (Fin k)) (a b : Bool) (j : Fin k) :
    (is.map (fun i => Sum.inl (i, a) : Fin k → Alphabet k B)).count (Sum.inl (j, b)) =
      if a = b then is.count j else 0 := by
  induction is with
  | nil => simp
  | cons i is ih =>
    cases a <;> cases b <;> simp [ih, List.count_cons]

theorem count_retained (i j : Fin k) :
    (retained i).count j = if j ≠ i ∧ j ≠ finRotate k i then 1 else 0 := by
  simp only [retained]
  split_ifs with h
  · rw [List.count_filter (by simpa only [decide_eq_true_eq] using h), List.count_finRange]
  · apply List.count_eq_zero.mpr
    simpa only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using h

theorem count_separator_left (i j : Fin k) (side : Bool) :
    (separator i : List (Alphabet k B)).count (Sum.inl (j, side)) =
      if j ≠ i ∧ j ≠ finRotate k i then 1 else 0 := by
  rw [separator, List.count_append]
  change ((retained i).map (fun j => Sum.inl (j, true) : Fin k → Alphabet k B)).count
      (Sum.inl (j, side)) +
    ((retained i).map (fun j => Sum.inl (j, false) : Fin k → Alphabet k B)).count
      (Sum.inl (j, side)) = _
  rw [count_side_list, count_side_list]
  cases side <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
    zero_add, add_zero, count_retained]

theorem count_separator_right (i : Fin k) (b : B) :
    (separator i : List (Alphabet k B)).count (Sum.inr b) = 0 := by
  simp [separator, x, y, List.count_eq_zero]

theorem rotate_ne (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  cases k with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · simp [hi] at hv
      omega
    · omega

theorem count_block_separator_balance (hk : 2 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) :
    (block r π i ++ separator i).count (Sum.inl (j, side)) +
      (if j = finRotate k i then 1 else 0) = 1 + (if j = i then 1 else 0) := by
  have hi := rotate_ne hk i
  simp only [List.count_append, count_block_left, count_separator_left]
  by_cases hji : j = i <;> by_cases hjr : j = finRotate k i <;>
    simp_all

theorem count_word_eq_sum (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (a : Alphabet k B) :
    (word r π).count a = ∑ i : Fin k, (block r π i ++ separator i).count a := by
  rw [word, List.count_flatMap, ← List.sum_toFinset _ (List.nodup_finRange k)]
  simp

/-- Each letter has exactly k occurrences in the displayed construction.
Uniformity already holds for k = 2; the representation proof requires k ≥ 3. -/
theorem word_uniform (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) :
    Crown.Uniform k (word r π) := by
  intro a
  rw [count_word_eq_sum]
  cases a with
  | inr b =>
    have hc : ∀ i, (block r π i ++ separator i).count (Sum.inr b) = 1 := by
      intro i
      simp only [List.count_append, count_block_right, count_separator_right, Nat.add_zero]
      exact List.count_eq_one_of_mem (hπ i).1 ((hπ i).2 b)
    simp [hc]
  | inl a =>
    obtain ⟨j, side⟩ := a
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => count_block_separator_balance hk r π i j side)
    have hr : (∑ i : Fin k, if j = finRotate k i then 1 else 0) = 1 := by
      rw [Equiv.sum_comp (finRotate k) (fun i => if j = i then (1 : ℕ) else 0)]
      simp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hr] at hs
    have hone : (∑ _i : Fin k, (1 : ℕ)) = k := by simp
    have hj : (∑ i : Fin k, if j = i then (1 : ℕ) else 0) = 1 := by simp
    rw [hone, hj] at hs
    omega

theorem restrictPair_cons (d : B) (l : List B) (b c : B) :
    Crown.restrictPair (d :: l) b c =
      if d = b ∨ d = c then d :: Crown.restrictPair l b c else Crown.restrictPair l b c := by
  simp [Crown.restrictPair, List.filter_cons]

theorem restrictPair_of_not_mem_left (l : List B) (b c : B) (hb : b ∉ l) :
    Crown.restrictPair l b c = l.filter (fun x => x = c) := by
  apply List.filter_congr
  intro d hd
  have hdb : d ≠ b := fun he => hb (he ▸ hd)
  simp [hdb]

/-- Restriction of a permutation to two distinct letters remembers their relative order. -/
theorem restrictPair_permutation (l : List B) (hn : l.Nodup) (b c : B)
    (hb : b ∈ l) (hc : c ∈ l) (hbc : b ≠ c) :
    Crown.restrictPair l b c = if l.idxOf b < l.idxOf c then [b, c] else [c, b] := by
  induction l with
  | nil => simp at hb
  | cons d l ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hdb : d = b
    · subst d
      have hcl : c ∈ l := (List.mem_cons.mp hc).resolve_left (Ne.symm hbc)
      have ht : Crown.restrictPair l b c = [c] := by
        rw [restrictPair_of_not_mem_left l b c hn'.1, List.filter_eq,
          List.count_eq_one_of_mem hn'.2 hcl]
        rfl
      simp [restrictPair_cons, ht, hbc]
    by_cases hdc : d = c
    · subst d
      have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
      have ht : Crown.restrictPair l b c = [b] := by
        rw [Crown.restrictPair_comm, restrictPair_of_not_mem_left l c b hn'.1,
          List.filter_eq, List.count_eq_one_of_mem hn'.2 hbl]
        rfl
      simp [restrictPair_cons, ht, hbc.symm]
    · have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left (Ne.symm hdb)
      have hcl : c ∈ l := (List.mem_cons.mp hc).resolve_left (Ne.symm hdc)
      have hh := ih hn'.2 hbl hcl
      simpa [restrictPair_cons, Orders.Before, List.idxOf_cons, hdb, hdc,
        Ne.symm hdb, Ne.symm hdc] using hh

def buckets (rank : B → Fin 5) (l : List B) : List B :=
  l.filter (fun b => rank b = 0) ++ l.filter (fun b => rank b = 1) ++
    l.filter (fun b => rank b = 2) ++ l.filter (fun b => rank b = 3) ++
      l.filter (fun b => rank b = 4)

omit [DecidableEq B] in
/-- Nondecreasing ranks make the five rank classes consecutive subwords. -/
theorem buckets_eq (rank : B → Fin 5) (l : List B)
    (hs : l.Pairwise (fun b c => rank b ≤ rank c)) : buckets rank l = l := by
  induction l with
  | nil => simp [buckets]
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := List.pairwise_cons.mp hs
    have hz : ∀ j : Fin 5, j < rank d → l.filter (fun b => rank b = j) = [] := by
      intro j hj
      apply List.filter_eq_nil_iff.mpr
      intro b hb he
      have he' : rank b = j := of_decide_eq_true he
      have hh := hd b hb
      rw [he'] at hh
      exact (not_le_of_gt hj) hh
    have hi := ih hl
    have hr : rank d = 0 ∨ rank d = 1 ∨ rank d = 2 ∨ rank d = 3 ∨ rank d = 4 := by
      have hv := (rank d).isLt
      simp only [Fin.ext_iff]
      omega
    conv_rhs => rw [← hi]
    rcases hr with hr | hr | hr | hr | hr <;>
      simp [buckets, hr, hz]

theorem pairwise_of_before (l : List B) (hn : l.Nodup) (rank : B → Fin 5)
    (hm : ∀ b c, Orders.Before l b c → rank b ≤ rank c) :
    l.Pairwise (fun b c => rank b ≤ rank c) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  apply hm
  simpa only [Orders.Before, hn.idxOf_getElem i hi, hn.idxOf_getElem j hj] using hij

def rightProjection (w : List (Alphabet k B)) : List B := w.filterMap Sum.getRight?

omit [DecidableEq B] in
theorem rightProjection_block (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (hs : (π i).Pairwise (fun b c => r b i ≤ r c i)) :
    rightProjection (block r π i) = π i := by
  simpa [rightProjection, block, gap, x, y, List.filterMap_map, List.filterMap_cons,
    Sum.getRight?, Function.comp_def,
    buckets] using buckets_eq (fun b => r b i) (π i) hs

omit [DecidableEq B] in
theorem rightProjection_separator (i : Fin k) :
    rightProjection (separator i : List (Alphabet k B)) = [] := by
  simp [rightProjection, separator, x, y, List.filterMap_map, Function.comp_def]

omit [DecidableEq B] in
theorem rightProjection_word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i)) :
    rightProjection (word r π) = (List.finRange k).flatMap π := by
  simp only [rightProjection, word, List.filterMap_flatMap]
  apply List.flatMap_congr
  intro i _
  change rightProjection (block r π i ++ separator i) = π i
  simp only [rightProjection, List.filterMap_append]
  change rightProjection (block r π i) ++ rightProjection (separator i) = π i
  rw [rightProjection_block r π i (hs i), rightProjection_separator, List.append_nil]

theorem restrictPair_rightProjection (w : List (Alphabet k B)) (b c : B) :
    Crown.restrictPair w (Sum.inr b) (Sum.inr c) =
      (Crown.restrictPair (rightProjection w) b c).map Sum.inr := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | inl a => simpa [Crown.restrictPair, rightProjection, List.filterMap_cons] using ih
    | inr a =>
      by_cases h : a = b ∨ a = c <;>
        simp [Crown.restrictPair, rightProjection, h] at ih ⊢ <;> exact ih

omit [DecidableEq B] in
theorem block_infix_word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) : block r π i <:+: word r π := by
  obtain ⟨as, bs, he⟩ := List.mem_iff_append.mp (List.mem_finRange i)
  refine ⟨as.flatMap (fun j => block r π j ++ separator j),
    separator i ++ bs.flatMap (fun j => block r π j ++ separator j), ?_⟩
  simp [word, he, List.flatMap_append, List.append_assoc]

theorem restrict_gap_left_pair (rank : B → Fin 5) (π : List B) (q : Fin 5)
    (a b : Fin k × Bool) :
    Crown.restrictPair (gap rank π q) (Sum.inl a) (Sum.inl b) = [] := by
  simp [Crown.restrictPair, gap, List.filter_map, Function.comp_def]

theorem different_pair_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (s t : Bool) (hij : i ≠ j) :
    ¬ Crown.Alternates (word r π) (Sum.inl (i, s)) (Sum.inl (j, t)) := by
  have hr : Crown.restrictPair (block r π i) (Sum.inl (i, s)) (Sum.inl (j, t)) =
      [Sum.inl (i, s), Sum.inl (i, s)] := by
    simp only [block, Crown.restrictPair_append, restrict_gap_left_pair]
    cases s <;> cases t <;>
      simp [Crown.restrictPair, x, y, hij]
  apply Crown.not_alternates_of_repeat (x := Sum.inl (i, s))
  rw [← hr]
  exact List.IsInfix.filter _ (block_infix_word r π i)

def pairChunk (b c : B) (t : Bool) : List B := if t then [b, c] else [c, b]

omit [DecidableEq B] in
theorem pairChunk_front_eq (b c : B) (s t : Bool) (w : List B)
    (hc : (pairChunk b c s ++ pairChunk b c t ++ w).IsChain (· ≠ ·)) : s = t := by
  cases s <;> cases t <;> first | rfl | simp [pairChunk, List.isChain_cons_cons] at hc

omit [DecidableEq B] in
theorem pairChunks_same_head (b c : B) (t : Bool) (ts : List Bool)
    (hc : (pairChunk b c t ++ ts.flatMap (pairChunk b c)).IsChain (· ≠ ·)) :
    ∀ u ∈ ts, u = t := by
  induction ts generalizing t with
  | nil => simp
  | cons s ts ih =>
    have he : t = s := pairChunk_front_eq b c t s (ts.flatMap (pairChunk b c))
      (by simpa only [List.flatMap_cons, List.append_assoc] using hc)
    have ht : (pairChunk b c s ++ ts.flatMap (pairChunk b c)).IsChain (· ≠ ·) := by
      cases t <;> exact hc.tail.tail
    intro u hu
    rcases List.mem_cons.mp hu with hus | hu
    · exact hus.trans he.symm
    · exact (ih s ht u hu).trans he.symm

omit [DecidableEq B] in
theorem pairChunks_nonchain (b c : B) (ts : List Bool)
    (hf : false ∈ ts) (ht : true ∈ ts) :
    ¬ (ts.flatMap (pairChunk b c)).IsChain (· ≠ ·) := by
  intro hc
  cases ts with
  | nil => simp at hf
  | cons s ts =>
    have hh := pairChunks_same_head b c s ts hc
    cases s with
    | false => exact Bool.noConfusion (hh true (by simpa using ht))
    | true => exact Bool.noConfusion (hh false (by simpa using hf))

theorem permutations_nonedge (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) (b c : B) (hbc : b ≠ c)
    (hf : ∃ i, Orders.Before (π i) b c) (hr : ∃ i, Orders.Before (π i) c b) :
    ¬ Crown.Alternates ((List.finRange k).flatMap π) b c := by
  let ts : List Bool := (List.finRange k).map fun i => decide ((π i).idxOf b < (π i).idxOf c)
  have hrestrict : Crown.restrictPair ((List.finRange k).flatMap π) b c =
      ts.flatMap (pairChunk b c) := by
    simp only [Crown.restrictPair, List.filter_flatMap, ts, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    simpa only [Crown.restrictPair, pairChunk, decide_eq_true_eq] using
      restrictPair_permutation (π i) (hπ i).1 b c ((hπ i).2 b) ((hπ i).2 c) hbc
  have htrue : true ∈ ts := by
    obtain ⟨i, hi⟩ := hf
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩
  have hfalse : false ∈ ts := by
    obtain ⟨i, hi⟩ := hr
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, decide_eq_false (not_lt_of_gt hi)⟩
  unfold Crown.Alternates
  rw [hrestrict]
  exact pairChunks_nonchain b c ts hfalse htrue

theorem right_pair_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (b c : B) (hbc : b ≠ c)
    (hf : ∃ i, Orders.Before (π i) b c) (hr : ∃ i, Orders.Before (π i) c b) :
    ¬ Crown.Alternates (word r π) (Sum.inr b) (Sum.inr c) := by
  have hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i) :=
    fun i => pairwise_of_before (π i) (hπ i).1 (fun b => r b i) (hm i)
  unfold Crown.Alternates
  rw [restrictPair_rightProjection, rightProjection_word r π hs, List.isChain_map]
  simpa only [Sum.inr.injEq, ne_eq, Crown.Alternates] using permutations_nonedge π hπ b c hbc hf hr

theorem restrict_block_same_pair (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) : Crown.restrictPair (block r π j) (x i) (y i) =
      if j = i then [x i, y i, x i, y i] else [] := by
  simp only [block, x, y, Crown.restrictPair_append, restrict_gap_left_pair]
  by_cases h : j = i
  · subst j
    simp [Crown.restrictPair]
  · simp [Crown.restrictPair, h]

theorem restrict_side_list (js : List (Fin k)) (side : Bool) (i : Fin k) :
    Crown.restrictPair (js.map (fun j => Sum.inl (j, side) : Fin k → Alphabet k B))
      (x i) (y i) = List.replicate (js.count i) (Sum.inl (i, side)) := by
  cases side <;>
    simp [Crown.restrictPair, x, y, List.filter_map, Function.comp_def,
      List.filter_eq, List.map_replicate]

theorem restrict_separator_same_pair (i j : Fin k) :
    Crown.restrictPair (separator j : List (Alphabet k B)) (x i) (y i) =
      if i ≠ j ∧ i ≠ finRotate k j then [y i, x i] else [] := by
  rw [separator, Crown.restrictPair_append]
  change Crown.restrictPair ((retained j).map (fun j => Sum.inl (j, true))) (x i) (y i) ++
    Crown.restrictPair ((retained j).map (fun j => Sum.inl (j, false))) (x i) (y i) = _
  rw [restrict_side_list, restrict_side_list, count_retained]
  by_cases h : i ≠ j ∧ i ≠ finRotate k j <;> simp [h, x, y, -finRotate_apply]

def pairTokens (i j : Fin k) : List Bool :=
  (if j = i then [true, true] else []) ++
    if i ≠ j ∧ i ≠ finRotate k j then [false] else []

theorem restrict_word_same_pair (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) : Crown.restrictPair (word r π) (x i) (y i) =
      ((List.finRange k).flatMap (pairTokens i)).flatMap (pairChunk (x i : Alphabet k B) (y i)) := by
  simp only [word, Crown.restrictPair, List.filter_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro j _
  change Crown.restrictPair (block r π j ++ separator j) (x i) (y i) = _
  rw [Crown.restrictPair_append, restrict_block_same_pair, restrict_separator_same_pair]
  by_cases hj : j = i <;> by_cases hi : i ≠ j ∧ i ≠ finRotate k j <;>
    simp [pairTokens, pairChunk, hj, hi, -finRotate_apply]

theorem coordinate_avoiding_two (hk : 3 ≤ k) (a b : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b := by
  classical
  apply Classical.byContradiction
  intro hn
  have h : ∀ i : Fin k, i = a ∨ i = b := by
    intro i
    by_cases ha : i = a
    · exact Or.inl ha
    exact Or.inr (Classical.byContradiction (fun hb => hn ⟨i, ha, hb⟩))
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [Fin.ext_iff] at h0 h1 h2
  omega

theorem same_pair_nonedge (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) (i : Fin k) :
    ¬ Crown.Alternates (word r π) (x i) (y i) := by
  have ht : true ∈ (List.finRange k).flatMap (pairTokens i) := by
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [pairTokens]⟩
  have hf : false ∈ (List.finRange k).flatMap (pairTokens i) := by
    obtain ⟨j, hji, hjr⟩ := coordinate_avoiding_two hk i ((finRotate k).symm i)
    have hir : i ≠ finRotate k j := by
      intro he
      apply hjr
      rw [he, Equiv.symm_apply_apply]
    exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      by simp [pairTokens, hji, Ne.symm hji, hir, -finRotate_apply]⟩
  unfold Crown.Alternates
  rw [restrict_word_same_pair]
  exact pairChunks_nonchain (x i) (y i) _ hf ht

def RankAdjacent (q : Fin 5) (side : Bool) : Prop :=
  if side then q = 2 ∨ q = 3 else q = 1 ∨ q = 2

def beforeCount (q : Fin 5) (side : Bool) : ℕ :=
  (q.val + if side then 0 else 1) / 2

def crossLocal (q : Fin 5) (side : Bool) (a b : Alphabet k B) : List (Alphabet k B) :=
  List.replicate (beforeCount q side) a ++ [b] ++
    List.replicate (2 - beforeCount q side) a

theorem rank_cases (q : Fin 5) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
  have hq := q.isLt
  simp only [Fin.ext_iff]
  omega

omit [DecidableEq B] in
theorem crossLocal_edge (q : Fin 5) (side : Bool) (a b : Alphabet k B)
    (h : RankAdjacent q side) : crossLocal q side a b = [a, b, a] := by
  rcases rank_cases q with hq | hq | hq | hq | hq <;> subst q <;> cases side <;>
    simp [RankAdjacent, crossLocal, beforeCount] at h ⊢

omit [DecidableEq B] in
theorem crossLocal_nonedge (q : Fin 5) (side : Bool) (a b : Alphabet k B)
    (h : ¬ RankAdjacent q side) : ¬ (crossLocal q side a b).IsChain (· ≠ ·) := by
  rcases rank_cases q with hq | hq | hq | hq | hq <;> subst q <;> cases side <;>
    simp [RankAdjacent, crossLocal, beforeCount, List.isChain_cons_cons] at h ⊢

theorem restrict_gap_cross (rank : B → Fin 5) (π : List B) (q : Fin 5)
    (a : Fin k × Bool) (b : B) (hb : π.count b = 1) :
    Crown.restrictPair (gap rank π q) (Sum.inl a) (Sum.inr b) =
      if rank b = q then [Sum.inr b] else [] := by
  rw [restrictPair_of_not_mem_left _ _ _ (by simp [gap]), List.filter_eq, count_gap_right]
  by_cases h : rank b = q <;> simp [h, hb]

theorem restrict_block_cross (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) (b : B) (hb : (π j).count b = 1) :
    Crown.restrictPair (block r π j) (Sum.inl (i, side)) (Sum.inr b) =
      if j = i then crossLocal (r b i) side (Sum.inl (i, side)) (Sum.inr b)
      else [Sum.inr b] := by
  simp only [block, Crown.restrictPair_append, restrict_gap_cross _ _ _ _ _ hb]
  by_cases hji : j = i
  · subst j
    rcases rank_cases (r b i) with hq | hq | hq | hq | hq <;> cases side <;>
      simp [Crown.restrictPair, x, y, hq, crossLocal, beforeCount]
  · rcases rank_cases (r b j) with hq | hq | hq | hq | hq <;> cases side <;>
      simp [Crown.restrictPair, x, y, hq, hji]

theorem restrict_separator_cross (i j : Fin k) (side : Bool) (b : B) :
    Crown.restrictPair (separator j : List (Alphabet k B)) (Sum.inl (i, side)) (Sum.inr b) =
      if i ≠ j ∧ i ≠ finRotate k j then [Sum.inl (i, side)] else [] := by
  rw [Crown.restrictPair_comm, restrictPair_of_not_mem_left _ _ _
    (by simp [separator, x, y]), List.filter_eq, count_separator_left]
  by_cases h : i ≠ j ∧ i ≠ finRotate k j <;> simp [h, -finRotate_apply]

theorem cross_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : (π i).count b = 1)
    (hn : ¬ RankAdjacent (r b i) side) :
    ¬ Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) := by
  intro hc
  have hi := List.IsInfix.filter
    (fun a => decide (a = Sum.inl (i, side) ∨ a = Sum.inr b)) (block_infix_word r π i)
  have hlocal := List.IsChain.infix hc hi
  change (Crown.restrictPair (block r π i) (Sum.inl (i, side)) (Sum.inr b)).IsChain (· ≠ ·) at hlocal
  rw [restrict_block_cross r π i i side b hb, if_pos rfl] at hlocal
  exact crossLocal_nonedge (r b i) side (Sum.inl (i, side)) (Sum.inr b) hn hlocal

def edgeCell (a b : Alphabet k B) (i j : Fin k) : List (Alphabet k B) :=
  if j = i then [a, b, a] else if i = finRotate k j then [b] else [b, a]

omit [DecidableEq B] in
theorem edgeCell_nonempty (a b : Alphabet k B) (i j : Fin k) : edgeCell a b i j ≠ [] := by
  unfold edgeCell
  split_ifs <;> simp

omit [DecidableEq B] in
theorem edgeCell_chain (a b : Alphabet k B) (hab : a ≠ b) (i j : Fin k) :
    (edgeCell a b i j).IsChain (· ≠ ·) := by
  unfold edgeCell
  split_ifs <;> simp [List.isChain_cons_cons, hab, Ne.symm hab]

omit [DecidableEq B] in
theorem edgeCell_boundary (hk : 2 ≤ k) (a b : Alphabet k B) (hab : a ≠ b) (i j : Fin k) :
    ∀ u ∈ (edgeCell a b i j).getLast?, ∀ v ∈ (edgeCell a b i (finRotate k j)).head?, u ≠ v := by
  by_cases hji : j = i
  · subst j
    have hi := rotate_ne hk i
    simp only [edgeCell, if_neg hi]
    split_ifs <;> simp [hab]
  · by_cases hir : i = finRotate k j
    · have hjr : j ≠ finRotate k j := Ne.symm (rotate_ne hk j)
      simp [edgeCell, hir, hjr, Ne.symm hab, -finRotate_apply]
    · simp only [edgeCell, if_neg hji, if_neg hir, if_neg (Ne.symm hir)]
      split_ifs <;> simp [hab]

theorem finRange_successor_chain (k : ℕ) :
    (List.finRange k).IsChain (fun i j => j = finRotate k i) := by
  apply List.isChain_iff_getElem.mpr
  intro n hn
  simp only [List.length_finRange] at hn
  simp only [List.getElem_finRange]
  cases k with
  | zero => omega
  | succ m => exact (finRotate_of_lt (by omega : n < m)).symm

omit [DecidableEq B] in
theorem edgeCells_chain (hk : 2 ≤ k) (a b : Alphabet k B) (hab : a ≠ b) (i : Fin k) :
    ((List.finRange k).flatMap (edgeCell a b i)).IsChain (· ≠ ·) := by
  rw [List.flatMap_def]
  apply (List.isChain_flatten ?_).mpr
  · refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      exact edgeCell_chain a b hab i j
    · rw [List.isChain_map]
      apply (finRange_successor_chain k).imp
      intro j l he
      subst l
      exact edgeCell_boundary hk a b hab i j
  · intro he
    obtain ⟨j, _, hj⟩ := List.mem_map.mp he
    exact edgeCell_nonempty a b i j hj

theorem restrict_cell_edge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) (b : B) (hb : (π j).count b = 1)
    (he : RankAdjacent (r b i) side) :
    Crown.restrictPair (block r π j ++ separator j) (Sum.inl (i, side)) (Sum.inr b) =
      edgeCell (Sum.inl (i, side)) (Sum.inr b) i j := by
  rw [Crown.restrictPair_append, restrict_block_cross r π i j side b hb,
    restrict_separator_cross]
  by_cases hji : j = i
  · subst j
    simp [edgeCell, crossLocal_edge _ _ _ _ he]
  · by_cases hir : i = finRotate k j
    · have hjr : j ≠ finRotate k j := fun hh => hji (hh.trans hir.symm)
      simp [edgeCell, hir, hjr, -finRotate_apply]
    · simp [edgeCell, hji, Ne.symm hji, hir, -finRotate_apply]

theorem cross_edge (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : ∀ j, (π j).count b = 1)
    (he : RankAdjacent (r b i) side) :
    Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) := by
  have hw : Crown.restrictPair (word r π) (Sum.inl (i, side)) (Sum.inr b) =
      (List.finRange k).flatMap (edgeCell (Sum.inl (i, side)) (Sum.inr b) i) := by
    simp only [word, Crown.restrictPair, List.filter_flatMap]
    apply List.flatMap_congr
    intro j _
    exact restrict_cell_edge r π i j side b (hb j) he
  unfold Crown.Alternates
  rw [hw]
  exact edgeCells_chain hk _ _ (by simp) i

theorem cross_iff (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : ∀ j, (π j).count b = 1) :
    Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) ↔ RankAdjacent (r b i) side := by
  constructor
  · intro ha
    exact Classical.byContradiction (fun hn => cross_nonedge r π i side b (hb i) hn ha)
  · exact cross_edge hk r π i side b hb

theorem left_pair_nonedge (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (a b : Fin k × Bool) (hab : a ≠ b) :
    ¬ Crown.Alternates (word r π) (Sum.inl a) (Sum.inl b) := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  by_cases hij : i = j
  · subst j
    cases s <;> cases t
    · exact False.elim (hab rfl)
    · exact same_pair_nonedge hk r π i
    · rw [Crown.alternates_comm]
      exact same_pair_nonedge hk r π i
    · exact False.elim (hab rfl)
  · exact different_pair_nonedge r π i j s t hij

def rankGraph (r : B → Ranks.CompletedRow (Fin k)) : SimpleGraph (Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => RankAdjacent (r b p.1) p.2
    | Sum.inr b, Sum.inl p => RankAdjacent (r b p.1) p.2
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

/-- L06--L07: the explicit construction represents the graph prescribed by
the completed ranks, and has exactly k occurrences of every vertex. -/
theorem word_represents_rankGraph (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (ho : ∀ b c, b ≠ c → (∃ i, Orders.Before (π i) b c) ∧
      (∃ i, Orders.Before (π i) c b)) :
    Crown.Represents (rankGraph r) k (word r π) := by
  have hk2 : 2 ≤ k := by omega
  have hc : ∀ b j, (π j).count b = 1 :=
    fun b j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 b)
  refine ⟨by omega, word_uniform hk2 r π hπ, ?_⟩
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hn := left_pair_nonedge hk r π a b (fun he => hab (congrArg Sum.inl he))
      exact ⟨False.elim, fun ha => False.elim (hn ha)⟩
    | inr b => exact (cross_iff hk2 r π a.1 a.2 b (hc b)).symm
  | inr a =>
    cases b with
    | inl b =>
      rw [Crown.alternates_comm]
      exact (cross_iff hk2 r π b.1 b.2 a (hc a)).symm
    | inr b =>
      have hab' : a ≠ b := fun he => hab (congrArg Sum.inr he)
      have hn := right_pair_nonedge r π hπ hm a b hab' (ho a b hab').1 (ho a b hab').2
      exact ⟨False.elim, fun ha => False.elim (hn ha)⟩

/-- The graph of an initial rank table. Choosing zero for stars specifies
its adjacency only; it makes no assertion that this completion is feasible. -/
def initialRankGraph (rows : B → Ranks.InitialRow (Fin k)) : SimpleGraph (Alphabet k B) :=
  rankGraph (fun b => Ranks.complete (rows b) false)

theorem completion_preserves_adjacency (ρ : Ranks.InitialRow (Fin k))
    (r : Ranks.CompletedRow (Fin k)) (hr : Ranks.Completes ρ r) (i : Fin k) (side : Bool) :
    RankAdjacent (r i) side ↔ RankAdjacent (Ranks.complete ρ false i) side := by
  cases hi : ρ i with
  | none =>
    have he : r i = 0 ∨ r i = 4 := by simpa [hi] using hr i
    rcases he with he | he <;> cases side <;>
      simp [RankAdjacent, Ranks.complete, Ranks.completeEntry, hi, he]
  | some u =>
    have he : r i = Ranks.prescribed u := by simpa [hi] using hr i
    simp [Ranks.complete, Ranks.completeEntry, hi, he]

theorem completion_graph_eq (rows : B → Ranks.InitialRow (Fin k))
    (r : B → Ranks.CompletedRow (Fin k)) (hr : ∀ b, Ranks.Completes (rows b) (r b)) :
    rankGraph r = initialRankGraph rows := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => exact completion_preserves_adjacency (rows b) (r b) (hr b) a.1 a.2
  | inr a =>
    cases b with
    | inl b => exact completion_preserves_adjacency (rows a) (r a) (hr a) b.1 b.2
    | inr b => rfl

/-- A feasible oriented rank table gives a genuine k-uniform graph representation.
The vertex type contains every paired endpoint and every row label, including
distinct labels with identical rows. -/
theorem feasible_representable [Fintype B] (hk : 3 ≤ k)
    (rows : B → Ranks.InitialRow (Fin k)) (hf : Ranks.Feasible rows) :
    Crown.KRepresentable (initialRankGraph rows) k := by
  obtain ⟨r, π, hr, hπ, hm, ho⟩ := Orders.feasible_coordinate_orders (by omega : 2 ≤ k) rows hf
  rw [← completion_graph_eq rows r hr]
  exact ⟨word r π, word_represents_rankGraph hk r π hπ hm ho⟩

#print axioms word_uniform
#print axioms restrictPair_permutation
#print axioms buckets_eq
#print axioms different_pair_nonedge
#print axioms right_pair_nonedge
#print axioms same_pair_nonedge
#print axioms cross_nonedge
#print axioms word_represents_rankGraph
#print axioms feasible_representable

end Crown.Blocks
