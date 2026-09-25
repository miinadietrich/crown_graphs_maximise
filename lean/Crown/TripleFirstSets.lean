import Crown.MatchingRanks

/-! The first-endpoint restriction for a central triple.
All incidence functions are arbitrary Boolean neighbourhoods on the full
vertex set. The matching coordinate choice only enumerates its pairs. -/

namespace Crown.TripleFirstSets
open Crown.Matchings Crown.MatchingRanks Crown.Orientations Crown.Ranks

noncomputable def rankRow {k : Nat} (N : Fin (2*k) → Bool) (p : OrientedPairing k) :
    InitialRow (Fin k) := row (neighbourRow N p) (fun _ => false)

def TriplePattern {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k) : Prop :=
  Fixed (rankRow l p) ∧ OneStar (rankRow c p) ∧ Fixed (rankRow u p) ∧
    PotentialBelow (rankRow l p) (rankRow c p) ∧
    PotentialBelow (rankRow c p) (rankRow u p)

theorem entry_zero_iff (b : Bool × Bool) :
    entry b false = some 0 ↔ b = (true,false) := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem entry_one_iff (b : Bool × Bool) :
    entry b false = some 1 ↔ b = (true,true) := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem entry_two_iff (b : Bool × Bool) :
    entry b false = some 2 ↔ b = (false,true) := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem outside_bits {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none)
    (i : Fin k) (hij : i ≠ j) :
    neighbourRow l p i = (true,false) ∧ neighbourRow c p i = (true,true) ∧
      neighbourRow u p i = (false,true) := by
  have hv := central_triple_values (rankRow l p) (rankRow c p) (rankRow u p)
    j h.1 h.2.1 h.2.2.1 hj h.2.2.2.1 h.2.2.2.2 i hij
  exact ⟨(entry_zero_iff _).mp hv.1, (entry_one_iff _).mp hv.2.1,
    (entry_two_iff _).mp hv.2.2⟩

theorem outside_neighbours {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none)
    (i : Fin k) (hij : i ≠ j) (b : Bool) :
    l (coordinates p (i,b)) = !b ∧ c (coordinates p (i,b)) = true ∧
      u (coordinates p (i,b)) = b := by
  have hv := outside_bits l c u p h j hj i hij
  cases b with
  | false => exact ⟨congrArg Prod.fst hv.1, congrArg Prod.fst hv.2.1,
      congrArg Prod.fst hv.2.2⟩
  | true => exact ⟨congrArg Prod.snd hv.1, congrArg Prod.snd hv.2.1,
      congrArg Prod.snd hv.2.2⟩

theorem star_neighbours {k : Nat} (c : Fin (2*k) → Bool) (p : OrientedPairing k)
    (j : Fin k) (hj : rankRow c p j = none) (b : Bool) :
    c (coordinates p (j,b)) = false := by
  have hv := (entry_none_iff (neighbourRow c p j) false).mp hj
  cases b with
  | false => exact congrArg Prod.fst hv
  | true => exact congrArg Prod.snd hv

theorem centre_nonneighbours {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none)
    (v : Fin (2*k)) :
    c v = false ↔ v = coordinates p (j,false) ∨ v = coordinates p (j,true) := by
  obtain ⟨⟨i,b⟩,rfl⟩ := (coordinates p).surjective v
  by_cases hij : i = j
  · subst i
    constructor
    · intro _
      cases b with
      | false => exact Or.inl rfl
      | true => exact Or.inr rfl
    · intro _
      exact star_neighbours c p j hj b
  · have hv := (outside_neighbours l c u p h j hj i hij b).2.1
    constructor
    · intro hf
      rw [hv] at hf
      contradiction
    · rintro (he | he)
      · exact False.elim (hij (congrArg Prod.fst ((coordinates p).injective he)))
      · exact False.elim (hij (congrArg Prod.fst ((coordinates p).injective he)))

theorem coordinate_ne_star {k : Nat} (p : OrientedPairing k) (j i : Fin k) (b : Bool)
    (ha : coordinates p (i,b) ≠ coordinates p (j,false))
    (hb : coordinates p (i,b) ≠ coordinates p (j,true)) : i ≠ j := by
  intro he
  subst i
  cases b with
  | false => exact ha rfl
  | true => exact hb rfl

theorem residual_first_set {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none)
    (v : Fin (2*k)) (ha : v ≠ coordinates p (j,false))
    (hb : v ≠ coordinates p (j,true)) : v ∈ p.1.val ↔ l v = true := by
  obtain ⟨⟨i,b⟩,rfl⟩ := (coordinates p).surjective v
  have hij := coordinate_ne_star p j i b ha hb
  have hv := (outside_neighbours l c u p h j hj i hij b).1
  cases b with
  | false => exact iff_of_true (coordinates_first_mem p i) hv
  | true => exact iff_of_false (coordinates_second_not_mem p i) (by
      rw [hv]
      decide)

theorem residual_neighbour_complements {k : Nat} (l c u : Fin (2*k) → Bool)
    (p : OrientedPairing k) (h : TriplePattern l c u p)
    (j : Fin k) (hj : rankRow c p j = none)
    (v : Fin (2*k)) (ha : v ≠ coordinates p (j,false))
    (hb : v ≠ coordinates p (j,true)) : u v = true ↔ l v = false := by
  obtain ⟨⟨i,b⟩,rfl⟩ := (coordinates p).surjective v
  have hij := coordinate_ne_star p j i b ha hb
  have hv := outside_neighbours l c u p h j hj i hij b
  rw [hv.1, hv.2.2]
  cases b <;> decide

theorem centre_degree {k : Nat} (l c u : Fin (2*k) → Bool) (p : OrientedPairing k)
    (h : TriplePattern l c u p) (j : Fin k) (hj : rankRow c p j = none) :
    (Finset.univ.filter (fun v => c v = true)).card = 2*k-2 := by
  have hz : Finset.univ.filter (fun v => c v = false) =
      {coordinates p (j,false), coordinates p (j,true)} := by
    ext v
    simp [centre_nonneighbours l c u p h j hj v]
  have hzcard : (Finset.univ.filter (fun v => c v = false)).card = 2 := by
    rw [hz]
    simp [coordinates_pair_distinct p j]
  have hp : ∀ v, (¬ c v = true) ↔ c v = false := by
    intro v
    cases c v <;> decide
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2*k)))) (fun v => c v = true)
  simp only [hp, hzcard, Finset.card_univ, Fintype.card_fin] at hsum
  omega

#print axioms centre_nonneighbours
#print axioms residual_first_set
#print axioms residual_neighbour_complements
#print axioms centre_degree
end Crown.TripleFirstSets
