import Crown.Cyclic
import Crown.Blocks

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem exists_segments (v : V) (w : List V) :
    ∃ p : List V, ∃ L : List (List V),
      w = p ++ L.flatMap (fun l => v :: l) ∧ v ∉ p ∧ ∀ l ∈ L, v ∉ l := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x w ih =>
    obtain ⟨p,L,hw,hp,hL⟩ := ih
    by_cases hx : x = v
    · subst x
      refine ⟨[],p::L,?_,by simp,?_⟩
      · simp [hw]
      · simpa using And.intro hp hL
    · refine ⟨x::p,L,?_,by simp [hx, Ne.symm hx,hp],hL⟩
      simp [hw]

theorem exists_segments_start (v : V) (w : List V) :
    ∃ L : List (List V), v :: w = L.flatMap (fun l => v :: l) ∧ ∀ l ∈ L, v ∉ l := by
  obtain ⟨p,L,hw,hp,hL⟩ := exists_segments v w
  exact ⟨p::L, by simp [hw], by simpa using And.intro hp hL⟩

theorem count_separator (v : V) (L : List (List V)) (hL : ∀ l ∈ L, v ∉ l) :
    (L.flatMap (fun l => v :: l)).count v = L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have hl := hL l (by simp)
    have ht : ∀ t ∈ L, v ∉ t := fun t ht => hL t (by simp [ht])
    simp [List.count_cons, List.count_eq_zero.mpr hl, ih ht]

theorem segment_infix (v : V) (L : List (List V)) (l : List V) (hl : l ∈ L) :
    l <:+: L.flatMap (fun t => v :: t) := by
  obtain ⟨p,s,hL⟩ := List.mem_iff_append.mp hl
  refine ⟨p.flatMap (fun t => v :: t) ++ [v], s.flatMap (fun t => v :: t), ?_⟩
  simp [hL, List.flatMap_append, List.append_assoc]

theorem repeat_chain_le_one (a : V) (n : ℕ)
    (h : (List.replicate n a).IsChain (· ≠ ·)) : n ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => simp [List.replicate_succ, List.isChain_cons_cons] at h

theorem segment_neighbour_count_le (v a : V) (L : List (List V))
    (hL : ∀ l ∈ L, v ∉ l) (hc : Crown.Alternates (L.flatMap (fun l => v :: l)) v a)
    (l : List V) (hl : l ∈ L) : l.count a ≤ 1 := by
  have hi := List.IsInfix.filter (fun x => decide (x = v ∨ x = a)) (segment_infix v L l hl)
  have hh := List.IsChain.infix hc hi
  change (Crown.restrictPair l v a).IsChain (· ≠ ·) at hh
  rw [Blocks.restrictPair_of_not_mem_left l v a (hL l hl), List.filter_eq] at hh
  exact repeat_chain_le_one a _ hh

theorem sum_le_length (ns : List ℕ) (hn : ∀ n ∈ ns, n ≤ 1) : ns.sum ≤ ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hh := hn n (by simp)
    have ht := ih (fun m hm => hn m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons]
    omega

theorem all_one_of_sum_eq_length (ns : List ℕ) (hn : ∀ n ∈ ns, n ≤ 1)
    (he : ns.sum = ns.length) : ∀ n ∈ ns, n = 1 := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hh := hn n (by simp)
    have ht : ∀ m ∈ ns, m ≤ 1 := fun m hm => hn m (by simp [hm])
    have hs := sum_le_length ns ht
    simp only [List.sum_cons, List.length_cons] at he
    have hn1 : n = 1 := by omega
    have he' : ns.sum = ns.length := by omega
    simpa only [List.mem_cons, forall_eq_or_imp, hn1, true_and] using ih ht he'

theorem segment_neighbour_count (v a : V) (hva : v ≠ a) (L : List (List V))
    (hL : ∀ l ∈ L, v ∉ l) (hc : Crown.Alternates (L.flatMap (fun l => v :: l)) v a)
    (he : (L.flatMap (fun l => v :: l)).count a = L.length) :
    ∀ l ∈ L, l.count a = 1 := by
  have hsum : (L.map (fun l => l.count a)).sum = L.length := by
    simpa only [List.count_flatMap, Function.comp_def, List.count_cons, beq_iff_eq, hva,
      if_false, Nat.zero_add, Nat.add_zero] using he
  have hle : ∀ n ∈ L.map (fun l => l.count a), n ≤ 1 := by
    intro n hn
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hn
    exact segment_neighbour_count_le v a L hL hc l hl
  have hall := all_one_of_sum_eq_length (L.map (fun l => l.count a)) hle
    (by simpa only [List.length_map] using hsum)
  intro l hl
  exact hall _ (List.mem_map.mpr ⟨l,hl,rfl⟩)

#print axioms exists_segments_start
#print axioms segment_neighbour_count

end Crown.CrownLower
