import Crown.CrownLowerOrder

/-! The between-occurrences lemma in the lower-bound proof, expressed through
actual permutation blocks and the first letters of binary restrictions. -/

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem permutation_prefix_bound (A : Set V) (L : List (List V))
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b : V) (ha : a ∈ A) (hb : b ∈ A) :
    ∀ p, p <+: L.flatten → p.count a ≤ p.count b + 1 := by
  induction L with
  | nil =>
    intro p hp
    have hp' : p = [] := by simpa using hp
    subst p
    simp
  | cons l L ih =>
    have hl := hL l (by simp)
    have ht : ∀ t ∈ L, IsPermutationOf A t := fun t ht => hL t (by simp [ht])
    have hca : l.count a = 1 := List.count_eq_one_of_mem hl.1 ((hl.2 a).mpr ha)
    have hcb : l.count b = 1 := List.count_eq_one_of_mem hl.1 ((hl.2 b).mpr hb)
    intro p hp
    change p <+: l ++ L.flatten at hp
    rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append l L.flatten) with hpl | hlp
    · have hle := List.Sublist.count_le a hpl.sublist
      omega
    · obtain ⟨t,rfl⟩ := hlp
      have htp : t <+: L.flatten := List.prefix_append_right_inj l |>.mp hp
      have hi := ih ht t htp
      simpa only [List.count_append,hca,hcb,Nat.add_assoc] using Nat.add_le_add_left hi 1

theorem filtered_permutation_prefix_bound (A : Set V) [DecidablePred (· ∈ A)]
    (w : List V) (L : List (List V)) (hw : w.filter (fun a => a ∈ A) = L.flatten)
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b : V) (ha : a ∈ A) (hb : b ∈ A) :
    ∀ p, p <+: w → p.count a ≤ p.count b + 1 := by
  intro p hp
  have hpf := hp.filter (fun a => decide (a ∈ A))
  rw [hw] at hpf
  have h := permutation_prefix_bound A L hL a b ha hb _ hpf
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha),
    List.count_filter (p := fun x => decide (x ∈ A)) (a := b) (by simpa using hb)] at h
  exact h

/-- Lemma 2 of Glen--Kitaev--Pyatkin: if an external common neighbour lies
between the first occurrences of two letters of a permutation-split set,
those two letters must alternate. The first-occurrence hypotheses use the
heads of binary restrictions, so they do not conflate repeated occurrences. -/
theorem between_permutations {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hrep : Crown.Represents G k w) (A : Set V) [DecidablePred (· ∈ A)]
    (L : List (List V)) (hw : w.filter (fun a => a ∈ A) = L.flatten)
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b x : V)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hax : G.Adj a x) (hxb : G.Adj x b)
    (hafirst : ∀ y ∈ (Crown.restrictPair w a x).head?, y = a)
    (hxfirst : ∀ y ∈ (Crown.restrictPair w x b).head?, y = x) : G.Adj a b := by
  apply (hrep.2.2 a b hab).mpr
  apply alternates_of_between w a b x hab
  · exact (prefixOrder_iff_directedChain w a x (G.ne_of_adj hax)).mpr
      ⟨(hrep.2.2 a x (G.ne_of_adj hax)).mp hax,hafirst⟩
  · exact (prefixOrder_iff_directedChain w x b (G.ne_of_adj hxb)).mpr
      ⟨(hrep.2.2 x b (G.ne_of_adj hxb)).mp hxb,hxfirst⟩
  · exact filtered_permutation_prefix_bound A w L hw hL a b ha hb

#print axioms permutation_prefix_bound
#print axioms between_permutations

end Crown.CrownLower
