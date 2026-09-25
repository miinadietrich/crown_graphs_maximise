import Crown.MatchingFirstSetCounts
import Crown.TripleDegrees

/-! The central-triple count. A fixed central pair and a specified ordering
of the two outer rows determine the entire remaining first-endpoint set. -/

namespace Crown.MatchingTripleCounts
open Crown.Matchings Crown.MatchingFirstSetCounts Crown.MatchingRanks Crown.TripleFirstSets
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def candidateSet {k : ℕ} (N : Fin (2*k) → Bool) (a b : Fin (2*k)) : Finset (Fin (2*k)) :=
  insert a (Finset.univ.filter (fun v => v ≠ a ∧ v ≠ b ∧ N v = true))

theorem firstSet_eq_candidate {k : ℕ} (N : Fin (2*k) → Bool) (p : OrientedPairing k)
    (a b : Fin (2*k)) (ha : a ∈ p.1.val) (hb : b ∉ p.1.val)
    (hres : ∀ v, v ≠ a → v ≠ b → (v ∈ p.1.val ↔ N v = true)) :
    p.1.val = candidateSet N a b := by
  have hab : a ≠ b := fun he => hb (he ▸ ha)
  ext v
  by_cases hva : v = a
  · subst v
    simp [candidateSet,ha]
  by_cases hvb : v = b
  · subst v
    simp [candidateSet,hb,hab.symm]
  simp [candidateSet,hva,hvb,hres v hva hvb]

theorem triple_firstSet_pair {k : ℕ} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (a b : Fin (2*k)) (hab : a ≠ b)
    (hshape : ∀ v, c v = false ↔ v = a ∨ v = b) :
    (p.1.val = candidateSet l a b ∧ DirectedPair (constrainedEquiv k p) a b) ∨
      (p.1.val = candidateSet l b a ∧ DirectedPair (constrainedEquiv k p) b a) := by
  obtain ⟨j,hj,_⟩ := h.2.1
  have ha := (centre_nonneighbours l c u p h j hj a).mp ((hshape a).mpr (Or.inl rfl))
  have hb := (centre_nonneighbours l c u p h j hj b).mp ((hshape b).mpr (Or.inr rfl))
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · left
    have hpair : DirectedPair (constrainedEquiv k p) a b := by
      rw [ha,hb]
      exact coordinates_directedPair p j
    refine ⟨firstSet_eq_candidate l p a b hpair.1 hpair.2.1 ?_,hpair⟩
    intro v hva hvb
    exact residual_first_set l c u p h j hj v (ha ▸ hva) (hb ▸ hvb)
  · right
    have hpair : DirectedPair (constrainedEquiv k p) b a := by
      rw [ha,hb]
      exact coordinates_directedPair p j
    refine ⟨firstSet_eq_candidate l p b a hpair.1 hpair.2.1 ?_,hpair⟩
    intro v hvb hva
    exact residual_first_set l c u p h j hj v (hb ▸ hvb) (ha ▸ hva)
  · exact False.elim (hab (ha.trans hb.symm))

noncomputable def firstSetPairEvent {k : ℕ} (S : Finset (Fin (2*k))) (a b : Fin (2*k)) :
    Finset (OrientedPairing k) :=
  Finset.univ.filter (fun p => p.1.val = S ∧ DirectedPair (constrainedEquiv k p) a b)

theorem firstSetPairEvent_card_le {k : ℕ} (S : Finset (Fin (2*k))) (a b : Fin (2*k)) :
    (firstSetPairEvent S a b).card ≤ (k-1).factorial := by
  simpa only [firstSetPairEvent,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    card_firstSetPair_le S a b

noncomputable def orderedTripleEvent {k : ℕ} (l c u : Fin (2*k) → Bool) : Finset (OrientedPairing k) :=
  Finset.univ.filter (TriplePattern l c u)

theorem orderedTripleEvent_card_le {k : ℕ} (l c u : Fin (2*k) → Bool)
    (a b : Fin (2*k)) (hab : a ≠ b) (hshape : ∀ v, c v = false ↔ v = a ∨ v = b) :
    (orderedTripleEvent l c u).card ≤ 2 * (k-1).factorial := by
  have hsub : orderedTripleEvent l c u ⊆
      firstSetPairEvent (candidateSet l a b) a b ∪ firstSetPairEvent (candidateSet l b a) b a := by
    intro p hp
    have h := triple_firstSet_pair l c u p (Finset.mem_filter.mp hp).2 a b hab hshape
    simpa only [firstSetPairEvent,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using h
  calc
    _ ≤ (firstSetPairEvent (candidateSet l a b) a b ∪ firstSetPairEvent (candidateSet l b a) b a).card :=
      Finset.card_le_card hsub
    _ ≤ (firstSetPairEvent (candidateSet l a b) a b).card +
        (firstSetPairEvent (candidateSet l b a) b a).card := Finset.card_union_le ..
    _ ≤ 2 * (k-1).factorial := by
      have h1 := firstSetPairEvent_card_le (candidateSet l a b) a b
      have h2 := firstSetPairEvent_card_le (candidateSet l b a) b a
      omega

noncomputable def tripleEvent {k : ℕ} (l c u : Fin (2*k) → Bool) : Finset (OrientedPairing k) :=
  orderedTripleEvent l c u ∪ orderedTripleEvent u c l

theorem tripleEvent_card_le {k : ℕ} (l c u : Fin (2*k) → Bool) :
    (tripleEvent l c u).card ≤ 4 * (k-1).factorial := by
  by_cases he : (tripleEvent l c u).Nonempty
  · obtain ⟨p,hp⟩ := he
    have hshape : ∃ a b : Fin (2*k), a ≠ b ∧ ∀ v, c v = false ↔ v = a ∨ v = b := by
      rcases Finset.mem_union.mp hp with hp | hp
      · have h := (Finset.mem_filter.mp hp).2
        obtain ⟨j,hj,_⟩ := h.2.1
        exact ⟨coordinates p (j,false),coordinates p (j,true),coordinates_pair_distinct p j,
          centre_nonneighbours l c u p h j hj⟩
      · have h := (Finset.mem_filter.mp hp).2
        obtain ⟨j,hj,_⟩ := h.2.1
        exact ⟨coordinates p (j,false),coordinates p (j,true),coordinates_pair_distinct p j,
          centre_nonneighbours u c l p h j hj⟩
    obtain ⟨a,b,hab,hshape⟩ := hshape
    have h1 := orderedTripleEvent_card_le l c u a b hab hshape
    have h2 := orderedTripleEvent_card_le u c l a b hab hshape
    have hcard := Finset.card_union_le (orderedTripleEvent l c u) (orderedTripleEvent u c l)
    change (orderedTripleEvent l c u ∪ orderedTripleEvent u c l).card ≤ 4 * (k-1).factorial
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp

theorem tripleEvent5_card_le (l c u : Fin 10 → Bool) :
    (tripleEvent (k := 5) l c u).card ≤ 96 := by
  simpa [Nat.factorial] using tripleEvent_card_le (k := 5) l c u

theorem triple_bound_ratio (k : ℕ) :
    (4 * k.factorial : ℚ) / Arithmetic.Q (k+1) = Arithmetic.theta (k+1) := by
  have h1 : 2*(k+1)-1 = 2*k+1 := by omega
  have h2 : 2*(k+1)-2 = 2*k := by omega
  have h3 : k+1-1 = k := by omega
  rw [Arithmetic.theta,h1,h2,h3,Q_succ,← choose_mul_factorial_eq_Q]
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hc : (Nat.choose (2*k) k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ 2*k)).ne'
  push_cast
  field_simp
  norm_num

theorem triple_probability_le {k : ℕ} (hk : 1 ≤ k) (l c u : Fin (2*k) → Bool) :
    ((tripleEvent l c u).card : ℚ) / Arithmetic.Q k ≤ Arithmetic.theta k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hn : ((tripleEvent l c u).card : ℚ) ≤ 4 * (m.factorial : ℚ) := by
    exact_mod_cast tripleEvent_card_le l c u
  calc
    _ ≤ (4 * m.factorial : ℚ) / Arithmetic.Q (m+1) :=
      div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
    _ = Arithmetic.theta (m+1) := triple_bound_ratio m

#print axioms triple_firstSet_pair
#print axioms tripleEvent_card_le
#print axioms tripleEvent5_card_le
#print axioms triple_probability_le

end Crown.MatchingTripleCounts
