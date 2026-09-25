import Crown.MatchingProbabilities

namespace Crown.MatchingRanks

open Crown.Matchings Crown.MatchingProbabilities Crown.PairTypes Crown.Orientations Crown.Ranks
open scoped Classical

theorem coordinates_directedPair {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    DirectedPair (constrainedEquiv k p) (coordinates p (i,false)) (coordinates p (i,true)) := by
  refine ⟨coordinates_first_mem p i,coordinates_second_not_mem p i,?_⟩
  intro ha hb
  apply Subtype.ext
  rfl

theorem directedPair_coordinates {k : ℕ} (p : OrientedPairing k) (a b : Fin (2*k))
    (h : DirectedPair (constrainedEquiv k p) a b) :
    ∃ i : Fin k, coordinates p (i,false) = a ∧ coordinates p (i,true) = b := by
  obtain ⟨i,hi⟩ := (firstCoordinates p.1).surjective ⟨a,h.1⟩
  refine ⟨i,congrArg Subtype.val hi,?_⟩
  change (p.2 (firstCoordinates p.1 i)).val = b
  rw [hi]
  exact congrArg Subtype.val (h.2.2 h.1 h.2.1)

noncomputable def pairColours {k : ℕ} (col : Fin (2*k) → Colour)
    (p : OrientedPairing k) : Fin k → Colour × Colour :=
  fun i => (col (coordinates p (i,false)),col (coordinates p (i,true)))

theorem comparison_coordinates {k : ℕ} (col : Fin (2*k) → Colour) (p : OrientedPairing k) :
    Comparison col (constrainedEquiv k p) ↔
      (∀ i, Allowed (pairColours col p i).1 (pairColours col p i).2) ∧
      AtMostOneExceptional (pairColours col p) := by
  constructor
  · intro h
    refine ⟨fun i => h.1 _ _ (coordinates_directedPair p i),?_⟩
    intro i j hi hj
    have he := h.2 _ _ _ _ (coordinates_directedPair p i) (coordinates_directedPair p j) hi hj
    exact congrArg Prod.fst ((coordinates p).injective he)
  · rintro ⟨hall,huniq⟩
    constructor
    · intro a b hab
      obtain ⟨i,rfl,rfl⟩ := directedPair_coordinates p a b hab
      exact hall i
    · intro a b c d hab hcd heab hecd
      obtain ⟨i,rfl,rfl⟩ := directedPair_coordinates p a b hab
      obtain ⟨j,rfl,rfl⟩ := directedPair_coordinates p c d hcd
      exact congrArg (fun i => coordinates p (i,false)) (huniq i j heab hecd)

theorem comparison_iff_rank {k : ℕ} (col : Fin (2*k) → Colour) (p : OrientedPairing k) :
    Comparison col (constrainedEquiv k p) ↔
      ¬ DoubleStar (smaller (pairColours col p)) ∧
      ¬ DoubleStar (larger (pairColours col p)) ∧
      StrictBelow (zeroRow (smaller (pairColours col p)) (fun _ => false))
        (zeroRow (larger (pairColours col p)) (fun _ => false)) := by
  rw [comparison_coordinates]
  exact (global_directed_iff (pairColours col p)).symm

noncomputable def neighbourRow {k : ℕ} (N : Fin (2*k) → Bool) (p : OrientedPairing k) :
    NeighbourRow (Fin k) :=
  fun i => (N (coordinates p (i,false)),N (coordinates p (i,true)))

def incidenceColour {k : ℕ} (N M : Fin (2*k) → Bool) : Fin (2*k) → Colour :=
  fun v => colourOfBits (N v,M v)

theorem smaller_incidence {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    smaller (pairColours (incidenceColour N M) p) = neighbourRow N p := by
  funext i
  simp [smaller,pairColours,incidenceColour,neighbourRow,bits_colourOfBits]

theorem larger_incidence {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    larger (pairColours (incidenceColour N M) p) = neighbourRow M p := by
  funext i
  simp [larger,pairColours,incidenceColour,neighbourRow,bits_colourOfBits]

theorem incidence_comparison_iff_rank {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    Comparison (incidenceColour N M) (constrainedEquiv k p) ↔
      ¬ DoubleStar (neighbourRow N p) ∧ ¬ DoubleStar (neighbourRow M p) ∧
      StrictBelow (zeroRow (neighbourRow N p) (fun _ => false))
        (zeroRow (neighbourRow M p) (fun _ => false)) := by
  rw [comparison_iff_rank,smaller_incidence,larger_incidence]

theorem pairBad_iff_comparison {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    PairBad (neighbourRow N p) (neighbourRow M p) (fun _ => false) ↔
      Comparison (incidenceColour N M) (constrainedEquiv k p) ∨
      Comparison (incidenceColour M N) (constrainedEquiv k p) := by
  rw [incidence_comparison_iff_rank,incidence_comparison_iff_rank]
  unfold PairBad
  tauto

theorem opposite_comparisons_disjoint {k : ℕ} (hk : 0 < k)
    (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    ¬ (Comparison (incidenceColour N M) (constrainedEquiv k p) ∧
      Comparison (incidenceColour M N) (constrainedEquiv k p)) := by
  rintro ⟨h,h'⟩
  have hab := ((incidence_comparison_iff_rank N M p).mp h).2.2 ⟨0,hk⟩
  have hba := ((incidence_comparison_iff_rank M N p).mp h').2.2 ⟨0,hk⟩
  exact (lt_asymm hab hba)

#print axioms comparison_iff_rank
#print axioms pairBad_iff_comparison
#print axioms opposite_comparisons_disjoint

end Crown.MatchingRanks
