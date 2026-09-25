import Crown.CrownLowerGeometry

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem pair_head_of_prefix (u v : List V) (a b : V) (ha : a ∈ u) (hb : b ∉ u) :
    (Crown.restrictPair (u++v) a b).head? = some a := by
  rw [Crown.restrictPair_append,Crown.restrictPair_comm u a b,
    Blocks.restrictPair_of_not_mem_left u b a hb,List.filter_eq]
  have hc := List.count_pos_iff.mpr ha
  cases he : u.count a with
  | zero => omega
  | succ n => simp [List.replicate_succ]

theorem blockWord_filter (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) :
    (blockWord D).filter (fun a => a ∈ A) =
      (D.map (fun d => d.1.filter (fun a => a ∈ A))).flatten := by
  unfold blockWord
  rw [List.filter_flatMap,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro d hd
  simpa only [Function.comp_def,List.filter_append,(hD d hd).2.1,List.append_nil]

theorem blockWord_permutations (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) :
    ∀ l ∈ D.map (fun d => d.1.filter (fun a => a ∈ A)), IsPermutationOf A l := by
  intro l hl
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hl
  exact (hD d hd).1

theorem no_common_neighbour_in_first_core {G : SimpleGraph V} {k : ℕ}
    (A : Set V) [DecidablePred (· ∈ A)] (d : List V × List V)
    (D : List (List V × List V))
    (hrep : Crown.Represents G k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock A t) (a b x : V)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (has : StartsIn (fun y => decide (y = a)) d.1)
    (hbe : EndsIn (fun y => decide (y = b)) d.1)
    (hax : G.Adj a x) (hxb : G.Adj x b) : x ∉ d.1 := by
  intro hx
  obtain ⟨a',s,hs,ha'⟩ := has
  have haa : a' = a := by simpa using ha'
  subst a'
  obtain ⟨t,b',ht,hb'⟩ := hbe
  have hbb : b' = b := by simpa using hb'
  subst b'
  have hperm := (hD d (by simp)).1
  have hcount : d.1.count b = 1 := by
    have hh := List.count_eq_one_of_mem hperm.1 ((hperm.2 b).mpr hb)
    rw [List.count_filter (p := fun y => decide (y ∈ A)) (a := b) (by simpa using hb)] at hh
    exact hh
  have hbt : b ∉ t := by
    apply List.count_eq_zero.mp
    rw [ht,List.count_append] at hcount
    simpa using hcount
  have hxt : x ∈ t := by
    rw [ht,List.mem_append,List.mem_singleton] at hx
    exact hx.resolve_right (G.ne_of_adj hxb)
  have hafirst : ∀ y ∈ (Crown.restrictPair (blockWord (d::D)) a x).head?, y = a := by
    simp [blockWord,hs,Crown.restrictPair]
  have hxfirst : ∀ y ∈ (Crown.restrictPair (blockWord (d::D)) x b).head?, y = x := by
    have he : blockWord (d::D) = t ++ ([b] ++ d.2 ++ blockWord D) := by
      simp [blockWord,ht,List.append_assoc]
    rw [he,pair_head_of_prefix t _ x b hxt hbt]
    simp
  exact hnab (between_permutations hrep A _ (blockWord_filter A _ hD)
    (blockWord_permutations A _ hD) a b x ha hb hab hax hxb hafirst hxfirst)

#print axioms no_common_neighbour_in_first_core

end Crown.CrownLower
