import Crown.SmallGraphPrismFinite

namespace Crown.SmallGraphs

local instance : BEq (Fin 6) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Fin 6) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

/-- An adjacent letter cannot occur twice in a gap containing no copy of its neighbour. -/
theorem gap_adj_count_le_one {G : SimpleGraph (Fin 6)} {s t : List (Fin 6)} {v a b : Fin 6}
    (hr : Crown.Represents G 2 ((v::s) ++ v::t)) (hab : G.Adj a b)
    (hsa : s.count a = 0) : s.count b ≤ 1 := by
  have hs : a ∉ s := List.count_eq_zero.mp hsa
  have hi : s <:+: ((v::s) ++ v::t) := ⟨[v],v::t,by simp⟩
  have hif := List.IsInfix.filter (fun x => decide (x=a ∨ x=b)) hi
  have hchain := List.IsChain.infix ((hr.2.2 a b (G.ne_of_adj hab)).mp hab) hif
  change (Crown.restrictPair s a b).IsChain (· ≠ ·) at hchain
  rw [Crown.Blocks.restrictPair_of_not_mem_left s a b hs,List.filter_eq] at hchain
  exact Crown.CrownLower.repeat_chain_le_one b _ hchain

/-- Nonneighbours of the separator that are adjacent to each other occupy the same gap. -/
theorem prism_dense_gap {w : List (Fin 6)} (hw : Crown.Represents prism 2 w) :
    ∃ s t : List (Fin 6), Crown.Represents prism 2 (gapWord s t) ∧
      0 ∉ s ∧ 0 ∉ t ∧ s.count 4 = 2 ∧ s.count 5 = 2 ∧
      ∀ a : Fin 6, a = 1 ∨ a = 2 ∨ a = 3 → s.count a = 1 := by
  obtain ⟨s,t,hr,hs,ht,ha⟩ := two_gaps hw 0
  have h4 : s.count 4 = 0 ∨ s.count 4 = 2 := by
    have hc := gap_counts hr (by decide : (4:Fin 6) ≠ 0)
    have hn : s.count 4 ≠ 1 := fun h => (by decide : ¬prism.Adj 0 4) ((ha 4 (by decide)).mpr h)
    omega
  have h5 : s.count 5 = 0 ∨ s.count 5 = 2 := by
    have hc := gap_counts hr (by decide : (5:Fin 6) ≠ 0)
    have hn : s.count 5 ≠ 1 := fun h => (by decide : ¬prism.Adj 0 5) ((ha 5 (by decide)).mpr h)
    omega
  have ha45 : prism.Adj 4 5 := by decide +kernel
  have hneigh : ∀ a : Fin 6, a = 1 ∨ a = 2 ∨ a = 3 → s.count a = 1 := by
    intro a h
    rcases h with rfl | rfl | rfl <;> apply (ha _ (by decide)).mp <;> decide
  rcases h4 with h4 | h4
  · have h5 : s.count 5 = 0 := h5.resolve_right (fun hh => by
      have hh' := gap_adj_count_le_one hr ha45 h4
      omega)
    have hc4 := gap_counts hr (by decide : (4:Fin 6) ≠ 0)
    have hc5 := gap_counts hr (by decide : (5:Fin 6) ≠ 0)
    refine ⟨t,s,Crown.represents_append_swap hr,ht,hs,by omega,by omega,?_⟩
    intro a ha'
    have hs1 := hneigh a ha'
    have hn : a ≠ 0 := by rcases ha' with rfl | rfl | rfl <;> decide
    have hc := gap_counts hr hn
    omega
  · have h5 : s.count 5 = 2 := h5.resolve_left (fun hh => by
      have hh' := gap_adj_count_le_one hr ha45.symm hh
      omega)
    exact ⟨s,t,hr,hs,ht,h4,h5,hneigh⟩

theorem prism_not_two : ¬Crown.KRepresentable prism 2 := by
  rintro ⟨w,hw⟩
  obtain ⟨s,t,hr,hs,ht,hs4,hs5,hn⟩ := prism_dense_gap hw
  have hs0 := List.count_eq_zero.mpr hs
  have ht0 := List.count_eq_zero.mpr ht
  have hs1 := hn 1 (by simp)
  have hs2 := hn 2 (by simp)
  have hs3 := hn 3 (by simp)
  have ht1 : t.count 1 = 1 := by have hc := gap_counts hr (by decide : (1:Fin 6) ≠ 0); omega
  have ht2 : t.count 2 = 1 := by have hc := gap_counts hr (by decide : (2:Fin 6) ≠ 0); omega
  have ht3 : t.count 3 = 1 := by have hc := gap_counts hr (by decide : (3:Fin 6) ≠ 0); omega
  have ht4 : t.count 4 = 0 := by have hc := gap_counts hr (by decide : (4:Fin 6) ≠ 0); omega
  have ht5 : t.count 5 = 0 := by have hc := gap_counts hr (by decide : (5:Fin 6) ≠ 0); omega
  have hp : s.Perm [(1:Fin 6),2,3,4,4,5,5] := by
    apply List.perm_iff_count.mpr
    intro a
    fin_cases a <;> simp [hs0,hs1,hs2,hs3,hs4,hs5]
  have hq : t.Perm [(1:Fin 6),2,3] := by
    apply List.perm_iff_count.mpr
    intro a
    fin_cases a <;> simp [ht0,ht1,ht2,ht3,ht4,ht5]
  exact prism_permutations_fail s (List.mem_permutations'.mpr hp)
    t (List.mem_permutations'.mpr hq) hr.2.2

#print axioms prism_dense_gap
#print axioms prism_not_two
end Crown.SmallGraphs
