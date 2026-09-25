import Crown.Blocks
import Crown.Cyclic

/-! The appended-word construction follows the Colbrook–Drysdale manuscript,
adapting Mozhui and Krishna, Section 2, *On the conjecture of the representation
number of bipartite graphs* (arXiv:2506.01057v1). Coordinates are numbered from zero. -/

namespace Crown.BaselineLiteral

open scoped BigOperators
open Crown.Blocks

variable {k : ℕ} {B : Type*} [DecidableEq B]
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

/-- y₁ x₁ rev(π₁) y₂ x₂ ... yₖ xₖ, with zero-based coordinates. -/
def extra (π : Fin k → List B) : List (Alphabet k B) :=
  (List.finRange k).flatMap fun i =>
    [y i,x i] ++ if i.val = 0 then (π i).reverse.map Sum.inr else []

def word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) :
    List (Alphabet k B) := Blocks.word r π ++ extra π

theorem extra_count_sum (π : Fin k → List B) (a : Alphabet k B) :
    (extra π).count a = ∑ i : Fin k,
      ([y i,x i] ++ if i.val = 0 then (π i).reverse.map Sum.inr else []).count a := by
  rw [extra,List.count_flatMap,← List.sum_toFinset _ (List.nodup_finRange k)]
  simp

theorem extra_count_left (π : Fin k → List B) (j : Fin k) (side : Bool) :
    (extra π).count (Sum.inl (j,side)) = 1 := by
  rw [extra_count_sum]
  have hc : ∀ i : Fin k,
      ([y i,x i] ++ if i.val = 0 then (π i).reverse.map Sum.inr else []).count
        (Sum.inl (j,side)) = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      cases side <;> split_ifs <;> simp_all [x,y,List.count_append,List.count_eq_zero]
    · cases side <;> split_ifs <;> simp_all [x,y,List.count_append,List.count_eq_zero,hij,Ne.symm hij]
  simp only [hc]
  simp

theorem extra_count_right (hk : 0 < k) (π : Fin k → List B) (b : B) :
    (extra π).count (Sum.inr b) = (π ⟨0,hk⟩).count b := by
  rw [extra_count_sum]
  have hc : ∀ i : Fin k,
      ([y i,x i] ++ if i.val = 0 then (π i).reverse.map Sum.inr else []).count (Sum.inr b) =
        if i = ⟨0,hk⟩ then (π i).count b else 0 := by
    intro i
    have hi : i.val = 0 ↔ i = ⟨0,hk⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    by_cases he : i = ⟨0,hk⟩
    · subst i
      simp [x,y,List.count_map_of_injective _ Sum.inr Sum.inr_injective]
    · simp [x,y,hi,he]
  simp only [hc]
  simp

theorem extra_uniform (hk : 0 < k) (π : Fin k → List B)
    (hπ : (π ⟨0,hk⟩).Nodup ∧ ∀ b, b ∈ π ⟨0,hk⟩) : Crown.Uniform 1 (extra π) := by
  intro a
  cases a with
  | inl p => exact extra_count_left π p.1 p.2
  | inr b =>
    rw [extra_count_right hk]
    exact List.count_eq_one_of_mem hπ.1 (hπ.2 b)

theorem word_uniform (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) :
    Crown.Uniform (k+1) (word r π) := by
  intro a
  simp only [word,List.count_append,Blocks.word_uniform hk r π hπ a,
    extra_uniform (by omega) π (hπ _) a]

theorem extra_successor {m : ℕ} (π : Fin (m+1) → List B) :
    extra π = [y 0,x 0] ++ (π 0).reverse.map Sum.inr ++
      (List.finRange m).flatMap (fun i => [y i.succ,x i.succ]) := by
  simp only [extra,List.finRange_succ,List.flatMap_cons,List.flatMap_map,Fin.val_zero,
    if_pos rfl,Fin.val_succ,Nat.add_eq_zero,one_ne_zero,and_false,if_false,List.append_nil]
  simp [List.append_assoc]

theorem rightProjection_extra (hk : 0 < k) (π : Fin k → List B) :
    Blocks.rightProjection (extra π) = (π ⟨0,hk⟩).reverse := by
  cases k with
  | zero => omega
  | succ m =>
    rw [extra_successor]
    simp [Blocks.rightProjection,List.filterMap_append,List.filterMap_flatMap,
      List.filterMap_map,List.filterMap_cons,List.filterMap_reverse,Sum.getRight?,x,y,Function.comp_def]

/-- Reversing the first permutation at the end breaks every pair of distinct
letters in that permutation. The middle factor is arbitrary, provided the
complete word has equal counts of the two letters. -/
theorem reverse_sandwich_nonedge (p q : List B) (b c : B) (hbc : b ≠ c)
    (hp : p.Nodup) (hb : b ∈ p) (hc : c ∈ p)
    (he : (p++q++p.reverse).count b = (p++q++p.reverse).count c) :
    ¬ Crown.Alternates (p++q++p.reverse) b c := by
  intro hchain
  have hrev : Crown.restrictPair p.reverse b c = (Crown.restrictPair p b c).reverse := by
    simp [Crown.restrictPair,List.filter_reverse]
  have hwhole : Crown.restrictPair (p++q++p.reverse) b c =
      Crown.restrictPair p b c ++ Crown.restrictPair q b c ++ (Crown.restrictPair p b c).reverse := by
    simp only [Crown.restrictPair_append,hrev]
  have hh := Crown.balanced_chain_endpoints b c hbc
    (Crown.restrictPair (p++q++p.reverse) b c) ?_ ?_ hchain
  · have hpp := Blocks.restrictPair_permutation p hp b c hb hc hbc
    by_cases hidx : p.idxOf b < p.idxOf c
    · simp only [hidx,if_true] at hpp
      have hhead : b ∈ (Crown.restrictPair (p++q++p.reverse) b c).head? := by
        rw [hwhole,hpp]
        simp [List.append_assoc]
      have hlast : b ∈ (Crown.restrictPair (p++q++p.reverse) b c).getLast? := by
        rw [hwhole,hpp]
        rw [List.getLast?_append]
        simp [List.append_assoc]
      exact hh b hhead b hlast rfl
    · simp only [hidx,if_false] at hpp
      have hhead : c ∈ (Crown.restrictPair (p++q++p.reverse) b c).head? := by
        rw [hwhole,hpp]
        simp [List.append_assoc]
      have hlast : c ∈ (Crown.restrictPair (p++q++p.reverse) b c).getLast? := by
        rw [hwhole,hpp]
        rw [List.getLast?_append]
        simp [List.append_assoc]
      exact hh c hhead c hlast rfl
  · intro a ha
    simpa [Crown.restrictPair] using (List.mem_filter.mp ha).2
  · simpa [Crown.restrictPair,List.count_filter] using he

theorem balanced_append_pair {V : Type*} [DecidableEq V]
    (u : List V) (a b : V) (hab : a ≠ b)
    (hm : ∀ x ∈ u, x = a ∨ x = b) (he : u.count a = u.count b)
    (hc : u.IsChain (· ≠ ·)) (hh : a ∈ u.head?) :
    (u ++ [a,b]).IsChain (· ≠ ·) := by
  have hend := Crown.balanced_chain_endpoints a b hab u hm he hc
  apply List.isChain_append.mpr
  refine ⟨hc,by simp [List.isChain_cons_cons,hab],?_⟩
  intro x hx y hy
  have hya : y = a := by simpa using hy.symm
  subst y
  exact Ne.symm (hend a hh x hx)

theorem cross_head (hk : 0 < k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (i : Fin k) (side : Bool) (b : B)
    (hb : ∀ j, (π j).count b = 1) (he : RankAdjacent (r b i) side) :
    (Crown.restrictPair (Blocks.word r π) (Sum.inl (i,side)) (Sum.inr b)).head? =
      some (if i.val = 0 then Sum.inl (i,side) else Sum.inr b) := by
  have hw : Crown.restrictPair (Blocks.word r π) (Sum.inl (i,side)) (Sum.inr b) =
      (List.finRange k).flatMap (edgeCell (Sum.inl (i,side)) (Sum.inr b) i) := by
    simp only [Blocks.word,Crown.restrictPair,List.filter_flatMap]
    apply List.flatMap_congr
    intro j hj
    exact restrict_cell_edge r π i j side b (hb j) he
  rw [hw]
  cases k with
  | zero => omega
  | succ m =>
    rw [List.finRange_succ,List.flatMap_cons]
    by_cases hi : i = 0
    · subst i
      simp [edgeCell]
    · have hv : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
      simp only [edgeCell,if_neg (Ne.symm hi)]
      split_ifs <;> simp_all [hv]

theorem extra_cross_restriction (hk : 0 < k) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : (π ⟨0,hk⟩).count b = 1) :
    Crown.restrictPair (extra π) (Sum.inl (i,side)) (Sum.inr b) =
      if i.val = 0 then [Sum.inl (i,side),Sum.inr b] else [Sum.inr b,Sum.inl (i,side)] := by
  cases k with
  | zero => omega
  | succ m =>
    have hb0 : (π 0).count b = 1 := hb
    let a : Alphabet (m+1) B := Sum.inl (i,side)
    let v : Alphabet (m+1) B := Sum.inr b
    let T : List (Alphabet (m+1) B) :=
      (List.finRange m).flatMap (fun j => [y j.succ,x j.succ])
    have hnot : v ∉ T := by simp [T,v,x,y]
    have ht : Crown.restrictPair T a v = List.replicate (T.count a) a := by
      rw [Crown.restrictPair_comm,Blocks.restrictPair_of_not_mem_left T v a hnot,List.filter_eq]
    have hm : Crown.restrictPair ((π 0).reverse.map Sum.inr) a v = [v] := by
      simp [Crown.restrictPair,a,v,List.filter_map,Function.comp_def,
        List.filter_eq,List.count_reverse,hb0,List.map_replicate]
    have hfirst : Crown.restrictPair [y 0,x 0] a v =
        if i = 0 then [a] else [] := by
      by_cases hi : i = 0
      · subst i
        cases side <;> simp [Crown.restrictPair,a,v,x,y]
      · cases side <;> simp [Crown.restrictPair,a,v,x,y,hi,Ne.symm hi]
    have hc : (if i = 0 then 1 else 0) + T.count a = 1 := by
      have hc := extra_count_left π i side
      rw [extra_successor] at hc
      have hzero : ((π 0).reverse.map Sum.inr : List (Alphabet (m+1) B)).count a = 0 := by
        simp [a,List.count_eq_zero]
      change ([y 0,x 0] ++ (π 0).reverse.map Sum.inr ++ T).count a = 1 at hc
      rw [List.count_append,List.count_append,hzero,Nat.add_zero] at hc
      have hf : ([y 0,x 0] : List (Alphabet (m+1) B)).count a = if i = 0 then 1 else 0 := by
        by_cases hi : i = 0
        · subst i
          cases side <;> simp [a,x,y]
        · cases side <;> simp [a,x,y,hi,Ne.symm hi]
      simpa only [hf] using hc
    rw [extra_successor,Crown.restrictPair_append,Crown.restrictPair_append]
    change Crown.restrictPair [y 0,x 0] a v ++
      Crown.restrictPair ((π 0).reverse.map Sum.inr) a v ++ Crown.restrictPair T a v = _
    rw [hfirst,hm,ht]
    by_cases hi : i = 0
    · have ht0 : T.count a = 0 := by simpa [hi] using hc
      rw [if_pos hi,ht0]
      have hv : i.val = 0 := congrArg Fin.val hi
      simp only [hv,if_true,List.replicate_zero,List.append_nil,List.singleton_append]
      rfl
    · have ht1 : T.count a = 1 := by simpa [hi] using hc
      have hv : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
      simp [hi,hv,ht1,a,v]

theorem cross_edge (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (i : Fin k) (side : Bool) (b : B) (he : RankAdjacent (r b i) side) :
    Crown.Alternates (word r π) (Sum.inl (i,side)) (Sum.inr b) := by
  have hb : ∀ j, (π j).count b = 1 :=
    fun j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 b)
  have hc := Blocks.cross_edge hk r π i side b hb he
  have hh := cross_head (by omega) r π i side b hb he
  have hm : ∀ v ∈ Crown.restrictPair (Blocks.word r π) (Sum.inl (i,side)) (Sum.inr b),
      v = Sum.inl (i,side) ∨ v = Sum.inr b := by
    intro v hv
    simpa [Crown.restrictPair] using (List.mem_filter.mp hv).2
  have hcount : (Crown.restrictPair (Blocks.word r π) (Sum.inl (i,side)) (Sum.inr b)).count (Sum.inl (i,side)) =
      (Crown.restrictPair (Blocks.word r π) (Sum.inl (i,side)) (Sum.inr b)).count (Sum.inr b) := by
    have hu := Blocks.word_uniform hk r π hπ
    simpa [Crown.restrictPair,List.count_filter] using
      (hu (Sum.inl (i,side))).trans (hu (Sum.inr b)).symm
  unfold Crown.Alternates word
  rw [Crown.restrictPair_append,extra_cross_restriction (by omega) π i side b (hb _)]
  by_cases hi : i.val = 0
  · simp only [hi,if_true] at hh ⊢
    exact balanced_append_pair _ _ _ (by simp) hm hcount hc (by simp [hh])
  · simp only [hi,if_false] at hh ⊢
    exact balanced_append_pair _ _ _ (by simp)
      (fun v hv => (hm v hv).symm) hcount.symm hc (by simp [hh])

theorem nonedge_persists {V : Type*} [DecidableEq V] (w u : List V) (a b : V)
    (h : ¬ Crown.Alternates w a b) : ¬ Crown.Alternates (w++u) a b := by
  intro hh
  exact h (List.IsChain.prefix hh (List.IsPrefix.filter _ (List.prefix_append w u)))

theorem right_pair_nonedge (hk : 0 < k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i))
    (b c : B) (hbc : b ≠ c) :
    ¬ Crown.Alternates (word r π) (Sum.inr b) (Sum.inr c) := by
  have hp : Blocks.rightProjection (word r π) =
      (List.finRange k).flatMap π ++ (π ⟨0,hk⟩).reverse := by
    unfold word Blocks.rightProjection
    rw [List.filterMap_append]
    change Blocks.rightProjection (Blocks.word r π) ++ Blocks.rightProjection (extra π) = _
    rw [Blocks.rightProjection_word r π hs,rightProjection_extra hk]
  unfold Crown.Alternates
  rw [Blocks.restrictPair_rightProjection,hp,List.isChain_map]
  simp only [ne_eq,Sum.inr.injEq]
  cases k with
  | zero => omega
  | succ m =>
    simp only [List.finRange_succ,List.flatMap_cons,List.flatMap_map]
    apply reverse_sandwich_nonedge (π 0) _ b c hbc (hπ 0).1 ((hπ 0).2 b) ((hπ 0).2 c)
    have hbcnt : ∀ j, (π j).count b = 1 :=
      fun j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 b)
    have hccnt : ∀ j, (π j).count c = 1 :=
      fun j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 c)
    simp [List.count_append,List.count_flatMap,List.count_reverse,Function.comp_def,hbcnt,hccnt]

theorem flatMap_single_index {A C : Type*} [DecidableEq A] (L : List A) (a : A) (v : List C) :
    L.flatMap (fun b => if b = a then v else []) = (List.replicate (L.count a) v).flatten := by
  induction L with
  | nil => simp
  | cons b L ih =>
    by_cases hba : b = a
    · subst b
      simp [List.count_cons,ih,List.replicate_succ]
    · simp [hba,List.count_cons,ih]

theorem extra_same_pair (π : Fin k → List B) (i : Fin k) :
    Crown.restrictPair (extra π) (x i) (y i) = [y i,x i] := by
  have hh : Crown.restrictPair (extra π) (x i) (y i) =
      (List.finRange k).flatMap (fun j => if j = i then [y i,x i] else []) := by
    simp only [extra,Crown.restrictPair,List.filter_flatMap]
    apply List.flatMap_congr
    intro j hj
    by_cases hji : j = i
    · subst j
      split_ifs <;> simp_all [x,y,List.filter_append,List.filter_map,Function.comp_def]
    · split_ifs <;> simp_all [x,y,hji,Ne.symm hji,List.filter_append,List.filter_map,Function.comp_def]
  rw [hh,flatMap_single_index,List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange i)]
  rfl

theorem same_pair_nonedge (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (i : Fin k) : ¬ Crown.Alternates (word r π) (x i) (y i) := by
  by_cases hk3 : 3 ≤ k
  · exact nonedge_persists _ _ _ _ (Blocks.same_pair_nonedge hk3 r π i)
  · have hk2 : k = 2 := by omega
    subst k
    have ht : ∀ j : Fin 2, (List.finRange 2).flatMap (pairTokens j) = [true,true] := by decide
    unfold Crown.Alternates word
    rw [Crown.restrictPair_append,Blocks.restrict_word_same_pair,ht i,extra_same_pair]
    simp [pairChunk,List.isChain_cons_cons]

theorem left_pair_nonedge (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (a b : Fin k × Bool) (hab : a ≠ b) :
    ¬ Crown.Alternates (word r π) (Sum.inl a) (Sum.inl b) := by
  obtain ⟨i,s⟩ := a
  obtain ⟨j,t⟩ := b
  by_cases hij : i = j
  · subst j
    cases s <;> cases t
    · exact False.elim (hab rfl)
    · exact same_pair_nonedge hk r π i
    · rw [Crown.alternates_comm]
      exact same_pair_nonedge hk r π i
    · exact False.elim (hab rfl)
  · exact nonedge_persists _ _ _ _ (Blocks.different_pair_nonedge r π i j s t hij)

/-- R02 in a stronger form: the displayed appended word works for every
completed rank table and every own-coordinate nondecreasing family of
permutations. Completing manuscript stars with zero is a special case. -/
theorem word_represents_rankGraph (hk : 2 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i) :
    Crown.Represents (Blocks.rankGraph r) (k+1) (word r π) := by
  have hc : ∀ b j, (π j).count b = 1 :=
    fun b j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 b)
  have hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i) :=
    fun i => Blocks.pairwise_of_before (π i) (hπ i).1 (fun b => r b i) (hm i)
  have hcross : ∀ i side b, RankAdjacent (r b i) side ↔
      Crown.Alternates (word r π) (Sum.inl (i,side)) (Sum.inr b) := by
    intro i side b
    refine ⟨cross_edge hk r π hπ i side b,?_⟩
    intro ha
    by_contra hn
    exact nonedge_persists _ _ _ _ (Blocks.cross_nonedge r π i side b (hc b i) hn) ha
  refine ⟨by omega,word_uniform hk r π hπ,?_⟩
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hn := left_pair_nonedge hk r π a b (fun he => hab (congrArg Sum.inl he))
      exact ⟨False.elim,fun ha => False.elim (hn ha)⟩
    | inr b => exact hcross a.1 a.2 b
  | inr a =>
    cases b with
    | inl b =>
      rw [Crown.alternates_comm]
      exact hcross b.1 b.2 a
    | inr b =>
      have hn := right_pair_nonedge (by omega) r π hπ hs a b (fun he => hab (congrArg Sum.inr he))
      exact ⟨False.elim,fun ha => False.elim (hn ha)⟩

/-- The zero-star completion and literal appended word required by R02. -/
theorem word_represents_initialRankGraph (hk : 2 ≤ k)
    (rows : B → Ranks.InitialRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c →
      Ranks.complete (rows b) false i ≤ Ranks.complete (rows c) false i) :
    Crown.Represents (Blocks.initialRankGraph rows) (k+1)
      (word (fun b => Ranks.complete (rows b) false) π) :=
  word_represents_rankGraph hk _ π hπ hm

#print axioms word_represents_initialRankGraph
#print axioms word_represents_rankGraph
#print axioms word_uniform
#print axioms right_pair_nonedge
#print axioms cross_edge
#print axioms extra_cross_restriction
#print axioms cross_head
#print axioms reverse_sandwich_nonedge

end Crown.BaselineLiteral
