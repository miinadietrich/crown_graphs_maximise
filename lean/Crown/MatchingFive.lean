import Crown.MatchingFixedCounts
import Crown.MatchingTripleCounts
import Crown.PairingWords

/-! The balanced ten-by-ten case from fixed-pair and central-triple events. -/

namespace Crown.MatchingFive

open Crown.Matchings Crown.MatchingRanks Crown.MatchingFixedCounts Crown.MatchingTripleCounts
open Crown.TripleFirstSets Crown.Orientations Crown.Ranks
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

noncomputable def fixedEvent (N M : Fin 10 → Bool) : Finset (OrientedPairing 5) :=
  Finset.univ.filter (fun p => FixedPairBad (neighbourRow N p) (neighbourRow M p))

theorem fixedEvent_card_le (N M : Fin 10 → Bool) : (fixedEvent N M).card ≤ 432 := by
  simpa only [fixedEvent,Nat.card_eq_fintype_card,Fintype.card_subtype] using fixedMatchingEvent5_le N M

theorem fixedPairBad_swap {I : Type*} (N M : NeighbourRow I) : FixedPairBad N M ↔ FixedPairBad M N := by
  unfold FixedPairBad
  tauto

noncomputable def pairFamily (N : Fin 10 → Fin 10 → Bool) (pair : Finset (Fin 10)) :
    Finset (OrientedPairing 5) :=
  Finset.univ.filter (fun p => ∃ l ∈ pair, ∃ u ∈ pair, l ≠ u ∧
    FixedPairBad (neighbourRow (N l) p) (neighbourRow (N u) p))

theorem pairFamily_pair (N : Fin 10 → Fin 10 → Bool) (l u : Fin 10) (hne : l ≠ u) :
    pairFamily N {l,u} = fixedEvent (N l) (N u) := by
  ext p
  simp only [pairFamily,fixedEvent,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,b,hb,hab,h⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact h
    · exact (fixedPairBad_swap _ _).mp h
    · exact False.elim (hab rfl)
  · intro h
    exact ⟨l,by simp,u,by simp,hne,h⟩

noncomputable def centres (N : Fin 10 → Fin 10 → Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun c => (Finset.univ.filter (fun a => N c a = true)).card = 8)

noncomputable def candidateTriples (N : Fin 10 → Fin 10 → Bool) : Finset (Fin 10 × Finset (Fin 10)) :=
  centres N ×ˢ (centres N)ᶜ.powersetCard 2

theorem candidateTriples_card_le (N : Fin 10 → Fin 10 → Bool) : (candidateTriples N).card ≤ 63 := by
  have hd : (centres N).card ≤ 10 := by simpa using (Finset.card_le_univ (centres N))
  simpa only [candidateTriples,Finset.card_product,Finset.card_powersetCard,Finset.card_compl,Fintype.card_fin]
    using Arithmetic.triple_candidates_five (centres N).card hd

noncomputable def tripleFamily (N : Fin 10 → Fin 10 → Bool) (tr : Fin 10 × Finset (Fin 10)) :
    Finset (OrientedPairing 5) :=
  Finset.univ.filter (fun p => ∃ l ∈ tr.2, ∃ u ∈ tr.2, l ≠ u ∧ TriplePattern (N l) (N tr.1) (N u) p)

theorem tripleFamily_pair (N : Fin 10 → Fin 10 → Bool) (c l u : Fin 10) (hne : l ≠ u) :
    tripleFamily N (c,{l,u}) = tripleEvent (k := 5) (N l) (N c) (N u) := by
  ext p
  simp only [tripleFamily,tripleEvent,orderedTripleEvent,Finset.mem_filter,Finset.mem_union,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,b,hb,hab,h⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hab rfl)
  · rintro (h | h)
    · exact ⟨l,by simp,u,by simp,hne,h⟩
    · exact ⟨u,by simp,l,by simp,hne.symm,h⟩

theorem tripleFamily_card_le (N : Fin 10 → Fin 10 → Bool)
    (tr : Fin 10 × Finset (Fin 10)) (htr : tr ∈ candidateTriples N) :
    (tripleFamily N tr).card ≤ 96 := by
  have hp := (Finset.mem_product.mp htr).2
  obtain ⟨l,u,hne,he⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
  rcases tr with ⟨c,pair⟩
  simp only at he
  subst pair
  rw [tripleFamily_pair N c l u hne]
  exact tripleEvent5_card_le (N l) (N c) (N u)

theorem candidate_of_triple (N : Fin 10 → Fin 10 → Bool) (p : OrientedPairing 5)
    (l c u : Fin 10) (h : TriplePattern (N l) (N c) (N u) p) :
    l ≠ u ∧ (c,{l,u}) ∈ candidateTriples N := by
  obtain ⟨j,hj,_⟩ := h.2.1
  have hc := centre_degree (N l) (N c) (N u) p h j hj
  have hl := lower_degree (N l) (N c) (N u) p h j hj
  have hu := upper_degree (N l) (N c) (N u) p h j hj
  have hne : l ≠ u := by
    intro he
    subst u
    obtain ⟨i,hij,_,_⟩ := coordinate_avoiding_three (by decide : 4 ≤ 5) j j j
    have hh := outside_bits (N l) (N c) (N l) p h j hj i hij
    have heq := hh.1.symm.trans hh.2.2
    cases heq
  refine ⟨hne,Finset.mem_product.mpr ⟨?_,?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_,by simp [hne]⟩
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    apply Finset.mem_compl.mpr
    intro hmem
    change b ∈ Finset.univ.filter (fun c => (Finset.univ.filter (fun a => N c a = true)).card = 8) at hmem
    have hdeg := (Finset.mem_filter.mp hmem).2
    rcases hb with hb | hb
    · subst b
      rcases hl with hl | hl
      · exact (by decide : (8 : ℕ) ≠ 5) (hdeg.symm.trans hl)
      · exact (by decide : (8 : ℕ) ≠ 6) (hdeg.symm.trans hl)
    · subst b
      rcases hu with hu | hu
      · exact (by decide : (8 : ℕ) ≠ 5) (hdeg.symm.trans hu)
      · exact (by decide : (8 : ℕ) ≠ 6) (hdeg.symm.trans hu)

theorem feasible_of_avoiding (N : Fin 10 → Fin 10 → Bool) (p : OrientedPairing 5)
    (hp : ∀ pair ∈ (Finset.univ : Finset (Fin 10)).powersetCard 2, p ∉ pairFamily N pair)
    (ht : ∀ tr ∈ candidateTriples N, p ∉ tripleFamily N tr) :
    Feasible (fun b => rankRow (N b) p) := by
  apply (feasible_iff_no_obstructions (by decide : 4 ≤ 5) _).mpr
  constructor
  · intro l u hl hu hpot
    have hs := (fixed_fixed_comparison hl hu false false).mpr hpot
    by_cases hne : l = u
    · subst u
      exact Nat.lt_irrefl _ (hs 0)
    · have hmem : ({l,u} : Finset (Fin 10)) ∈ Finset.univ.powersetCard 2 :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by simp [hne]⟩
      apply hp {l,u} hmem
      rw [pairFamily_pair N l u hne]
      simp only [fixedEvent,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hl,hu,Or.inl hs⟩
  · rintro ⟨c,⟨hc,u,hu,hcu⟩,⟨_,l,hl,hlc⟩⟩
    have htr : TriplePattern (N l) (N c) (N u) p := ⟨hl,hc,hu,hlc,hcu⟩
    obtain ⟨hne,hmem⟩ := candidate_of_triple N p l c u htr
    apply ht (c,{l,u}) hmem
    simp only [tripleFamily,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨l,by simp,u,by simp,hne,htr⟩

theorem exists_feasible_matching (N : Fin 10 → Fin 10 → Bool) :
    ∃ p : OrientedPairing 5, Feasible (fun b => rankRow (N b) p) := by
  have hpbound : ∀ pair ∈ (Finset.univ : Finset (Fin 10)).powersetCard 2,
      (pairFamily N pair).card ≤ 432 := by
    intro pair hmem
    obtain ⟨l,u,hne,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hmem).2
    rw [pairFamily_pair N l u hne]
    exact fixedEvent_card_le (N l) (N u)
  have hp : (∑ pair ∈ (Finset.univ : Finset (Fin 10)).powersetCard 2, (pairFamily N pair).card) ≤ 45*432 := by
    calc
      _ ≤ ∑ pair ∈ (Finset.univ : Finset (Fin 10)).powersetCard 2, 432 := Finset.sum_le_sum hpbound
      _ = 45*432 := by norm_num [Finset.card_powersetCard,Nat.choose]
  have ht : (∑ tr ∈ candidateTriples N, (tripleFamily N tr).card) ≤ 63*96 := by
    calc
      _ ≤ ∑ tr ∈ candidateTriples N, 96 := Finset.sum_le_sum (tripleFamily_card_le N)
      _ = (candidateTriples N).card * 96 := by simp
      _ ≤ 63*96 := Nat.mul_le_mul_right 96 (candidateTriples_card_le N)
  have hsmall : (∑ pair ∈ (Finset.univ : Finset (Fin 10)).powersetCard 2, (pairFamily N pair).card) +
      (∑ tr ∈ candidateTriples N, (tripleFamily N tr).card) <
      (Finset.univ : Finset (OrientedPairing 5)).card := by
    rw [Finset.card_univ,card_orientedPairing,Arithmetic.Q5]
    omega
  obtain ⟨p,_,hpair,htr⟩ := Counting.exists_avoiding_two_families
    ((Finset.univ : Finset (Fin 10)).powersetCard 2) (candidateTriples N)
    (Finset.univ : Finset (OrientedPairing 5)) (pairFamily N) (tripleFamily N) hsmall
  exact ⟨p,feasible_of_avoiding N p hpair htr⟩

theorem matrix_representable (M : Fin 10 → Fin 10 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 5 := by
  obtain ⟨p,hp⟩ := exists_feasible_matching (fun b a => M a b)
  exact Crown.PairingWords.of_feasible (by decide) (coordinates p) M hp

#print axioms candidateTriples_card_le
#print axioms exists_feasible_matching
#print axioms matrix_representable

end Crown.MatchingFive
