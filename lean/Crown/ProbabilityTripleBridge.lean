import Crown.ProbabilityRankBridge

/-! Coordinate transport of the full central-triple event. -/
namespace Crown.ProbabilitySpecification
open Crown.Matchings Crown.Ranks Crown.Orientations Crown.PairingCoordinates
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem fixed_reindex {I J : Type*} (e : I ≃ J) (r : InitialRow J) :
    Fixed (fun i => r (e i)) ↔ Fixed r := by
  constructor
  · intro h j
    simpa using h (e.symm j)
  · intro h i
    exact h (e i)

private theorem oneStar_reindex {I J : Type*} (e : I ≃ J) (r : InitialRow J) :
    OneStar (fun i => r (e i)) ↔ OneStar r := by
  constructor
  · rintro ⟨i,hi,hu⟩
    refine ⟨e i,hi,?_⟩
    intro j hj
    have he : e.symm j = i := hu (e.symm j) (by simpa using hj)
    simpa using congrArg e he
  · rintro ⟨j,hj,hu⟩
    refine ⟨e.symm j,by simpa using hj,?_⟩
    intro i hi
    apply e.injective
    simpa using hu (e i) hi

private theorem potential_reindex {I J : Type*} (e : I ≃ J) (r s : InitialRow J) :
    PotentialBelow (fun i => r (e i)) (fun i => s (e i)) ↔ PotentialBelow r s := by
  constructor
  · intro h j
    simpa using h (e.symm j)
  · intro h i
    exact h (e i)

theorem triple_realizes {k : ℕ} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (e : Coordinates k) (he : Realizes (constrainedEquiv k p) e) :
    TriplePattern l c u e ↔ Crown.TripleFirstSets.TriplePattern l c u p := by
  have hp : ofCoordinates e = p := (constrainedEquiv k).injective (realized_pairing _ _ he)
  obtain ⟨σ,hσ⟩ := Crown.PairingCoverage.coordinate_change e (coordinates p) (hp.trans (of_canonical p).symm)
  have hr (N : Fin (2*k) → Bool) :
      rankRow N e = fun i => Crown.TripleFirstSets.rankRow N p (σ i) := by
    funext i
    change entry (N (e (i,false)),N (e (i,true))) false =
      entry (N (coordinates p (σ i,false)),N (coordinates p (σ i,true))) false
    rw [hσ i false,hσ i true]
  rw [TriplePattern,Crown.TripleFirstSets.TriplePattern,hr l,hr c,hr u]
  simp only [fixed_reindex,oneStar_reindex,potential_reindex]

theorem triple_event_iff {k : ℕ} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k) :
    TripleEvent l c u (constrainedEquiv k p) ↔
      p ∈ Crown.MatchingTripleCounts.tripleEvent l c u := by
  simp only [Crown.MatchingTripleCounts.tripleEvent,Finset.mem_union,
    Crown.MatchingTripleCounts.orderedTripleEvent,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,h|h⟩
    · exact Or.inl ((triple_realizes l c u p e he).mp h)
    · exact Or.inr ((triple_realizes u c l p e he).mp h)
  · intro h
    refine ⟨coordinates p,coordinates_realize p,?_⟩
    rcases h with h | h
    · exact Or.inl ((triple_realizes l c u p _ (coordinates_realize p)).mpr h)
    · exact Or.inr ((triple_realizes u c l p _ (coordinates_realize p)).mpr h)

theorem triple_event_card {k : ℕ} (l c u : Fin (2*k) → Bool) :
    Nat.card {p : PairingOn (Fin (2*k)) // TripleEvent l c u p} =
      (Crown.MatchingTripleCounts.tripleEvent l c u).card := by
  let e := Equiv.subtypeEquiv (constrainedEquiv k)
    (fun p => (triple_event_iff l c u p).symm)
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem triple_probability (k : ℕ) (hk : 1 ≤ k) (l c u : Fin (2*k) → Bool) :
    (Nat.card {p : PairingOn (Fin (2*k)) // TripleEvent l c u p} : ℚ) /
      Crown.Arithmetic.Q k ≤ Crown.Arithmetic.theta k := by
  rw [triple_event_card]
  exact Crown.MatchingTripleCounts.triple_probability_le hk l c u

theorem triple_degrees {k : ℕ} (l c u : Fin (2*k) → Bool) (e : Coordinates k)
    (h : TriplePattern l c u e) :
    Nat.card {v : Fin (2*k) // c v = true} = 2*k-2 ∧
    (Nat.card {v : Fin (2*k) // l v = true} = k ∨
      Nat.card {v : Fin (2*k) // l v = true} = k+1) ∧
    (Nat.card {v : Fin (2*k) // u v = true} = k ∨
      Nat.card {v : Fin (2*k) // u v = true} = k+1) := by
  let p := ofCoordinates e
  have he : Realizes (constrainedEquiv k p) e := fun a b => directed_ofCoordinates e a b
  have hp := (triple_realizes l c u p e he).mp h
  obtain ⟨j,hj,_⟩ := hp.2.1
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using
    And.intro (Crown.TripleFirstSets.centre_degree l c u p hp j hj)
      ⟨Crown.TripleFirstSets.lower_degree l c u p hp j hj,
       Crown.TripleFirstSets.upper_degree l c u p hp j hj⟩

theorem triple_residual_sets {k : ℕ} (l c u : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (h : TripleEvent l c u p)
    (a b : Fin (2*k)) (hab : a ≠ b) (hc : ∀ v, c v = false ↔ v = a ∨ v = b) :
    (DirectedPair p a b ∨ DirectedPair p b a) ∧
      ((∀ v, v ≠ a → v ≠ b → (v ∈ p.1 ↔ l v = true)) ∨
       (∀ v, v ≠ a → v ≠ b → (v ∈ p.1 ↔ u v = true))) := by
  let q := (constrainedEquiv k).symm p
  have hp : constrainedEquiv k q = p := (constrainedEquiv k).apply_symm_apply p
  have hh : q ∈ Crown.MatchingTripleCounts.tripleEvent l c u :=
    (triple_event_iff l c u q).mp (hp.symm ▸ h)
  simp only [Crown.MatchingTripleCounts.tripleEvent,Finset.mem_union,
    Crown.MatchingTripleCounts.orderedTripleEvent,Finset.mem_filter,Finset.mem_univ,true_and] at hh
  have shape (L U : Fin (2*k) → Bool) (ht : Crown.TripleFirstSets.TriplePattern L c U q) :
      (DirectedPair p a b ∨ DirectedPair p b a) ∧
        ∀ v, v ≠ a → v ≠ b → (v ∈ p.1 ↔ L v = true) := by
    rcases Crown.MatchingTripleCounts.triple_firstSet_pair L c U q ht a b hab hc with
      ⟨hs,hpair⟩ | ⟨hs,hpair⟩
    · refine ⟨Or.inl (hp ▸ hpair),?_⟩
      intro v hva hvb
      rw [← hp]
      change v ∈ q.1.val ↔ L v = true
      rw [hs]
      simp [Crown.MatchingTripleCounts.candidateSet,hva,hvb]
    · refine ⟨Or.inr (hp ▸ hpair),?_⟩
      intro v hva hvb
      rw [← hp]
      change v ∈ q.1.val ↔ L v = true
      rw [hs]
      simp [Crown.MatchingTripleCounts.candidateSet,hva,hvb]
  rcases hh with hl | hu
  · exact ⟨(shape l u hl).1,Or.inl (shape l u hl).2⟩
  · exact ⟨(shape u l hu).1,Or.inr (shape u l hu).2⟩

#print axioms triple_realizes
#print axioms triple_event_card
#print axioms triple_probability
#print axioms triple_degrees
#print axioms triple_residual_sets
end Crown.ProbabilitySpecification
