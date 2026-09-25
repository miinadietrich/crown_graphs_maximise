import Crown.TripleFirstSets

namespace Crown.TripleFirstSets
open Crown.Matchings Crown.MatchingRanks Crown.Orientations Crown.Ranks

/-- Replacing one distinguished first endpoint by one or both endpoints
changes the neighbourhood size by at most one. -/
theorem degree_of_residual_first_set {V : Type*} [Fintype V] [DecidableEq V]
    (N : V → Bool) (S : Finset V) (k : Nat) (hcard : S.card = k)
    (a b : V) (haS : a ∈ S) (hbS : b ∉ S)
    (hres : ∀ v, v ≠ a → v ≠ b → (v ∈ S ↔ N v = true))
    (hstar : N a = true ∨ N b = true) :
    (Finset.univ.filter (fun v => N v = true)).card = k ∨
      (Finset.univ.filter (fun v => N v = true)).card = k+1 := by
  have hab : a ≠ b := by
    rintro rfl
    exact hbS haS
  have hk : 0 < k := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨a,haS⟩
  cases ha : N a <;> cases hb : N b
  · simp [ha,hb] at hstar
  · have he : Finset.univ.filter (fun v => N v = true) = insert b (S.erase a) := by
      ext v
      by_cases hva : v = a
      · subst v
        simp [ha,hb,hab,hab.symm,haS,hbS]
      by_cases hvb : v = b
      · subst v
        simp [ha,hb,hab,hab.symm,haS,hbS]
      simp [hva,hvb,← hres v hva hvb]
    left
    rw [he, Finset.card_insert_of_notMem (by simp [hbS]), Finset.card_erase_of_mem haS, hcard]
    omega
  · have he : Finset.univ.filter (fun v => N v = true) = S := by
      ext v
      by_cases hva : v = a
      · subst v
        simp [ha,haS]
      by_cases hvb : v = b
      · subst v
        simp [hb,hbS]
      simp [← hres v hva hvb]
    exact Or.inl ((congrArg Finset.card he).trans hcard)
  · have he : Finset.univ.filter (fun v => N v = true) = insert b S := by
      ext v
      by_cases hva : v = a
      · subst v
        simp [ha,haS]
      by_cases hvb : v = b
      · subst v
        simp [hb]
      simp [hvb,← hres v hva hvb]
    right
    rw [he, Finset.card_insert_of_notMem hbS, hcard]

theorem fixed_star_has_neighbour {k : Nat} (N : Fin (2*k) → Bool)
    (p : OrientedPairing k) (h : Fixed (rankRow N p)) (j : Fin k) :
    N (coordinates p (j,false)) = true ∨ N (coordinates p (j,true)) = true := by
  have hn := h j
  by_cases ha : N (coordinates p (j,false)) = true
  · exact Or.inl ha
  right
  by_contra hb
  apply hn
  apply (entry_none_iff (neighbourRow N p j) false).mpr
  change (N (coordinates p (j,false)),N (coordinates p (j,true))) = (false,false)
  have hfa : N (coordinates p (j,false)) = false := Bool.eq_false_iff.mpr ha
  have hfb : N (coordinates p (j,true)) = false := Bool.eq_false_iff.mpr hb
  rw [hfa,hfb]

theorem lower_degree {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none) :
    (Finset.univ.filter (fun v => l v = true)).card = k ∨
      (Finset.univ.filter (fun v => l v = true)).card = k+1 :=
  degree_of_residual_first_set l p.1.val k p.1.property
    (coordinates p (j,false)) (coordinates p (j,true))
    (coordinates_first_mem p j) (coordinates_second_not_mem p j)
    (residual_first_set l c u p h j hj) (fixed_star_has_neighbour l p h.1 j)

theorem upper_degree {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none) :
    (Finset.univ.filter (fun v => u v = true)).card = k ∨
      (Finset.univ.filter (fun v => u v = true)).card = k+1 := by
  have hs : (p.1.valᶜ).card = k := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin, p.1.property]
    omega
  apply degree_of_residual_first_set u p.1.valᶜ k hs
    (coordinates p (j,true)) (coordinates p (j,false))
  · simpa using coordinates_second_not_mem p j
  · simpa using coordinates_first_mem p j
  · intro v hvb hva
    have hfirst := residual_first_set l c u p h j hj v hva hvb
    have hcomp := residual_neighbour_complements l c u p h j hj v hva hvb
    rw [Finset.mem_compl, hfirst, hcomp]
    cases l v <;> decide
  · exact (fixed_star_has_neighbour u p h.2.2.1 j).symm

#print axioms degree_of_residual_first_set
#print axioms lower_degree
#print axioms upper_degree
end Crown.TripleFirstSets
