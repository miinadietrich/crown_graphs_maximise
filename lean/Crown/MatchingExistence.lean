import Crown.MatchingBadCounts
import Crown.PairingWords

/-! Finite matching union bounds for the balanced cases k = 6 and k = 7. -/

namespace Crown.MatchingExistence

open Crown.Matchings Crown.MatchingProbabilities Crown.MatchingRanks Crown.MatchingBadCounts
open Crown.Orientations Crown.Ranks
open scoped Classical BigOperators

noncomputable def badMatchings {k : ℕ} (N M : Fin (2*k) → Bool) : Finset (OrientedPairing k) :=
  Finset.univ.filter (fun p => PairBad (neighbourRow N p) (neighbourRow M p) (fun _ => false))

theorem card_badMatchings (k : ℕ) (N M : Fin (2*(k+1)) → Bool) :
    (badMatchings N M).card =
      Arithmetic.P (k+1) (Fintype.card (ColourClass (incidenceColour N M) Crown.PairTypes.Colour.X))
        (Fintype.card (ColourClass (incidenceColour N M) Crown.PairTypes.Colour.Y))
        (Fintype.card (ColourClass (incidenceColour N M) Crown.PairTypes.Colour.Z))
        (Fintype.card (ColourClass (incidenceColour N M) Crown.PairTypes.Colour.T)) := by
  simpa only [badMatchings,Nat.card_eq_fintype_card,Fintype.card_subtype] using
    card_badMatchingEvent k N M

theorem badMatchings6_card_le (N M : Fin 12 → Bool) : (badMatchings (k := 6) N M).card ≤ 8640 := by
  rw [card_badMatchings 5]
  apply Arithmetic.P6_le
  simpa only [Fintype.card_fin] using colour_classes_card (incidenceColour (k := 6) N M)

theorem badMatchings7_card_le (N M : Fin 14 → Bool) : (badMatchings (k := 7) N M).card ≤ 86400 := by
  rw [card_badMatchings 6]
  apply Arithmetic.P7_le
  simpa only [Fintype.card_fin] using colour_classes_card (incidenceColour (k := 7) N M)

noncomputable def badPairFamily {k : ℕ} (N : Fin (2*k) → Fin (2*k) → Bool)
    (pair : Finset (Fin (2*k))) : Finset (OrientedPairing k) :=
  Finset.univ.filter (fun p =>
    ∃ b ∈ pair, ∃ c ∈ pair, b ≠ c ∧ PairBad (neighbourRow (N b) p) (neighbourRow (N c) p) (fun _ => false))

theorem badPairFamily_pair {k : ℕ} (N : Fin (2*k) → Fin (2*k) → Bool)
    (b c : Fin (2*k)) (hbc : b ≠ c) : badPairFamily N {b,c} = badMatchings (N b) (N c) := by
  ext p
  simp only [badPairFamily,badMatchings,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨u,hu,v,hv,huv,hbad⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (huv rfl)
    · exact hbad
    · exact (pairBad_swap _ _ _).mp hbad
    · exact False.elim (huv rfl)
  · intro hbad
    exact ⟨b,by simp,c,by simp,hbc,hbad⟩

theorem exists_feasible_matching_of_bound (k : ℕ) (hk : 0 < k) (bound : ℕ)
    (N : Fin (2*k) → Fin (2*k) → Bool)
    (hbound : ∀ b c, (badMatchings (N b) (N c)).card ≤ bound)
    (hsmall : Nat.choose (2*k) 2 * bound < Arithmetic.Q k) :
    ∃ p : OrientedPairing k, Feasible (fun b => row (neighbourRow (N b) p) (fun _ => false)) := by
  haveI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hpair : ∀ pair ∈ (Finset.univ : Finset (Fin (2*k))).powersetCard 2,
      (badPairFamily N pair).card ≤ bound := by
    intro pair hp
    obtain ⟨b,c,hbc,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
    rw [badPairFamily_pair N b c hbc]
    exact hbound b c
  have htotal : ((Finset.univ : Finset (Fin (2*k))).powersetCard 2).card * bound <
      (Finset.univ : Finset (OrientedPairing k)).card := by
    simpa only [Counting.card_vertex_pairs,Finset.card_univ,card_orientedPairing] using hsmall
  obtain ⟨p,_,hp⟩ := Counting.exists_avoiding_of_uniform_bound
    ((Finset.univ : Finset (Fin (2*k))).powersetCard 2)
    (Finset.univ : Finset (OrientedPairing k)) (badPairFamily N) bound hpair htotal
  refine ⟨p,feasible_of_no_pairBad (fun b => neighbourRow (N b) p) (fun _ => false) ?_⟩
  intro b c hbc hbad
  have hmem : ({b,c} : Finset (Fin (2*k))) ∈
      (Finset.univ : Finset (Fin (2*k))).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _,by simp [hbc]⟩
  apply hp {b,c} hmem
  rw [badPairFamily_pair N b c hbc]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩

theorem exists_feasible_matching6 (N : Fin 12 → Fin 12 → Bool) :
    ∃ p : OrientedPairing 6, Feasible (fun b => row (neighbourRow (N b) p) (fun _ => false)) := by
  apply exists_feasible_matching_of_bound 6 (by decide) 8640 N
  · intro b c
    exact badMatchings6_card_le (N b) (N c)
  · norm_num [Arithmetic.Q6,Nat.choose]

theorem exists_feasible_matching7 (N : Fin 14 → Fin 14 → Bool) :
    ∃ p : OrientedPairing 7, Feasible (fun b => row (neighbourRow (N b) p) (fun _ => false)) := by
  apply exists_feasible_matching_of_bound 7 (by decide) 86400 N
  · intro b c
    exact badMatchings7_card_le (N b) (N c)
  · norm_num [Arithmetic.Q7,Nat.choose]

theorem matrix_representable6 (M : Fin 12 → Fin 12 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 6 := by
  obtain ⟨p,hp⟩ := exists_feasible_matching6 (fun b a => M a b)
  exact Crown.PairingWords.of_feasible (by decide) (coordinates p) M hp

theorem matrix_representable7 (M : Fin 14 → Fin 14 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 7 := by
  obtain ⟨p,hp⟩ := exists_feasible_matching7 (fun b a => M a b)
  exact Crown.PairingWords.of_feasible (by decide) (coordinates p) M hp

#print axioms card_badMatchings
#print axioms exists_feasible_matching6
#print axioms exists_feasible_matching7
#print axioms matrix_representable6
#print axioms matrix_representable7

end Crown.MatchingExistence
