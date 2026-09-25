import Crown.UnorderedMatchingEnumeration

namespace Crown.UnorderedMatchings
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private instance {V : Type*} [Fintype V] [DecidableEq V] (P : Finset (Finset V)) :
    Decidable (IsPerfectPairing P) := by
  letI : Decidable (∀ e ∈ P, e.card = 2) :=
    @Finset.decidableDforallFinset _ P _ (fun e _ => inferInstance)
  unfold IsPerfectPairing
  infer_instance

private instance {V : Type*} [Fintype V] [LinearOrder V] (d : ℕ) (S : Finset V) :
    Decidable (∀ P ∈ enumerate d S, IsPerfectPairing P) :=
  @Finset.decidableDforallFinset _ _ _ (fun P _ => inferInstance)

private theorem enumerated_three_valid :
    ∀ P ∈ enumerate 3 (Finset.univ : Finset (Fin 6)), IsPerfectPairing P := by
  decide +kernel

private theorem enumerated_four_valid :
    ∀ P ∈ enumerate 4 (Finset.univ : Finset (Fin 8)), IsPerfectPairing P := by
  decide +kernel

private theorem families_eq_enumerate (k : ℕ)
    (hv : ∀ P ∈ enumerate k (Finset.univ : Finset (Fin (2*k))), IsPerfectPairing P) :
    families k = enumerate k Finset.univ := by
  ext P
  constructor
  · intro hp
    obtain ⟨he,hcard,hd⟩ := (mem_families k P).mp hp
    have hu := ((mem_families_iff_perfect k P).mp hp).2.2
    exact enumerate_complete k Finset.univ P he hd hu hcard
  · intro hp
    exact (mem_families_iff_perfect k P).mpr (hv P hp)

theorem families_three_card : (families 3).card = 15 := by
  rw [families_eq_enumerate 3 enumerated_three_valid]
  decide +kernel

theorem families_four_card : (families 4).card = 105 := by
  rw [families_eq_enumerate 4 enumerated_four_valid]
  decide +kernel

theorem pairings_three_card : Fintype.card (Pairings 3) = 15 := by
  simpa only [Fintype.card_coe] using families_three_card

theorem pairings_four_card : Fintype.card (Pairings 4) = 105 := by
  simpa only [Fintype.card_coe] using families_four_card

/-- The manuscript's literal unordered partitions of six vertices. -/
theorem perfect_pairings_six_card :
    Nat.card {P : Finset (Finset (Fin 6)) // IsPerfectPairing P} = 15 := by
  rw [← Nat.card_congr (semanticEquiv 3),Nat.card_eq_fintype_card]
  exact pairings_three_card

/-- The manuscript's literal unordered partitions of eight vertices. -/
theorem perfect_pairings_eight_card :
    Nat.card {P : Finset (Finset (Fin 8)) // IsPerfectPairing P} = 105 := by
  rw [← Nat.card_congr (semanticEquiv 4),Nat.card_eq_fintype_card]
  exact pairings_four_card

#print axioms perfect_pairings_six_card
#print axioms perfect_pairings_eight_card
#print axioms families_three_card
#print axioms families_four_card
#print axioms pairings_three_card
#print axioms pairings_four_card
end Crown.UnorderedMatchings
