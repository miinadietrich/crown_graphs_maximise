import Crown.MatchingBadCounts

/-! Exact fixed/fixed comparison count, including colour classes with T vertices. -/

namespace Crown.MatchingFixedCounts

open Crown.Matchings Crown.MatchingCounts Crown.MatchingProbabilities Crown.MatchingBadCounts
open Crown.MatchingRanks Crown.PairTypes Crown.Orientations Crown.Ranks
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V]

theorem respects_no_T (col : V → Colour) (p : PairingOn V)
    (h : Respects p (ordinaryRelation col)) : ∀ v, col v ≠ Colour.T := by
  intro v hv
  obtain ⟨a,b,hab,ha | hb⟩ := vertex_incident p v
  · exact (ordinary_no_T _ _ (h a b hab)).1 (ha ▸ hv)
  · exact (ordinary_no_T _ _ (h a b hab)).2 (hb ▸ hv)

noncomputable def ordinaryNoTEquiv [Fintype V] (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T) :
    {p : PairingOn (ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) //
      DirectedCrossEvent (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z) p} ≃
    {p : PairingOn V // Respects p (ordinaryRelation col)} :=
  Equiv.subtypeEquiv (relabel (noTEquiv col ht)) (by
    intro p
    rw [respects_relabel,directedCrossEvent_respects]
    simp only [Respects,ordinaryRelation,noTEquiv_colour,ordinary_classColour]
    rfl)

theorem card_ordinary_noT [Fintype V] (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T)
    (k : ℕ) (hcard : Fintype.card V = 2*k) :
    Nat.card {p : PairingOn V // Respects p (ordinaryRelation col)} =
      Arithmetic.M k (Fintype.card (ColourClass col Colour.X)) (Fintype.card (ColourClass col Colour.Y))
        (Fintype.card (ColourClass col Colour.Z)) := by
  rw [← Nat.card_congr (ordinaryNoTEquiv col ht)]
  apply natCard_directedCrossEvent_finite
  have h := (Fintype.card_congr (noTEquiv col ht)).trans hcard
  simpa only [ClassVertices,Fintype.card_sum,Nat.add_assoc] using h

theorem card_ordinary [Fintype V] (col : V → Colour)
    (k : ℕ) (hcard : Fintype.card V = 2*k) :
    Nat.card {p : PairingOn V // Respects p (ordinaryRelation col)} =
      Arithmetic.M k (Fintype.card (ColourClass col Colour.X)) (Fintype.card (ColourClass col Colour.Y))
        (Fintype.card (ColourClass col Colour.Z)) := by
  by_cases ht : ∀ v, col v ≠ Colour.T
  · exact card_ordinary_noT col ht k hcard
  · push Not at ht
    obtain ⟨v,hv⟩ := ht
    haveI : IsEmpty {p : PairingOn V // Respects p (ordinaryRelation col)} :=
      ⟨fun p => respects_no_T col p.val p.property v hv⟩
    rw [Nat.card_of_isEmpty]
    have hp := Fintype.card_pos_iff.mpr (Nonempty.intro (⟨v,hv⟩ : ColourClass col Colour.T))
    change 0 < Fintype.card (ColourClass col Colour.T) at hp
    have hs := colour_classes_card col
    unfold Arithmetic.M
    split_ifs with h
    · omega
    · rfl

def FixedComparison (col : V → Colour) (p : PairingOn V) : Prop :=
  Respects p (ordinaryRelation col) ∨ Respects p (ordinaryRelation (fun v => swapColour (col v)))

theorem card_fixedComparison [Fintype V] [Nonempty V] (col : V → Colour)
    (k : ℕ) (hcard : Fintype.card V = 2*k) :
    Nat.card {p : PairingOn V // FixedComparison col p} =
      2 * Arithmetic.M k (Fintype.card (ColourClass col Colour.X)) (Fintype.card (ColourClass col Colour.Y))
        (Fintype.card (ColourClass col Colour.Z)) := by
  unfold FixedComparison
  rw [Nat.card_congr (subtypeOrEquiv _ _ (show Disjoint (fun p : PairingOn V => Respects p (ordinaryRelation col))
      (fun p => Respects p (ordinaryRelation (fun v => swapColour (col v)))) from by
    intro q h h' p hp
    obtain ⟨a,b,hab,_⟩ := vertex_incident p (Classical.choice (inferInstance : Nonempty V))
    exact allowed_swap_disjoint _ _ (Or.inl (h p hp a b hab)) (Or.inl (h' p hp a b hab)))),Nat.card_sum]
  rw [card_ordinary col k hcard,card_ordinary (fun v => swapColour (col v)) k hcard]
  simp only [card_colourClass_swap]
  simp only [swapColour]
  rw [Arithmetic.M_swap_xy (k : ℤ) (Fintype.card (ColourClass col Colour.Y) : ℤ)
    (Fintype.card (ColourClass col Colour.X) : ℤ) (Fintype.card (ColourClass col Colour.Z) : ℤ)]
  omega

theorem ordinary_iff_fixed_rank {k : ℕ} (col : Fin (2*k) → Colour) (p : OrientedPairing k) :
    Respects (constrainedEquiv k p) (ordinaryRelation col) ↔
      Fixed (row (smaller (pairColours col p)) (fun _ => false)) ∧
      Fixed (row (larger (pairColours col p)) (fun _ => false)) ∧
      StrictBelow (zeroRow (smaller (pairColours col p)) (fun _ => false))
        (zeroRow (larger (pairColours col p)) (fun _ => false)) := by
  rw [global_fixed_iff]
  constructor
  · intro h i
    exact h _ _ (coordinates_directedPair p i)
  · intro h a b hab
    obtain ⟨i,rfl,rfl⟩ := directedPair_coordinates p a b hab
    exact h i

def FixedPairBad {I : Type*} (N M : NeighbourRow I) : Prop :=
  Fixed (row N (fun _ => false)) ∧ Fixed (row M (fun _ => false)) ∧
    (StrictBelow (zeroRow N (fun _ => false)) (zeroRow M (fun _ => false)) ∨
      StrictBelow (zeroRow M (fun _ => false)) (zeroRow N (fun _ => false)))

theorem fixedPairBad_iff_fixedComparison {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    FixedPairBad (neighbourRow N p) (neighbourRow M p) ↔
      FixedComparison (incidenceColour N M) (constrainedEquiv k p) := by
  unfold FixedComparison
  rw [swap_incidenceColour,ordinary_iff_fixed_rank,ordinary_iff_fixed_rank,
    smaller_incidence,larger_incidence,smaller_incidence,larger_incidence]
  unfold FixedPairBad
  tauto

noncomputable def fixedMatchingEventEquiv {k : ℕ} (N M : Fin (2*k) → Bool) :
    {p : OrientedPairing k // FixedPairBad (neighbourRow N p) (neighbourRow M p)} ≃
    {p : PairingOn (Fin (2*k)) // FixedComparison (incidenceColour N M) p} :=
  Equiv.subtypeEquiv (constrainedEquiv k) (by intro p; exact fixedPairBad_iff_fixedComparison N M p)

theorem card_fixedMatchingEvent (k : ℕ) (hk : 0 < k) (N M : Fin (2*k) → Bool) :
    Nat.card {p : OrientedPairing k // FixedPairBad (neighbourRow N p) (neighbourRow M p)} =
      2 * Arithmetic.M k (Fintype.card (ColourClass (incidenceColour N M) Colour.X))
        (Fintype.card (ColourClass (incidenceColour N M) Colour.Y))
        (Fintype.card (ColourClass (incidenceColour N M) Colour.Z)) := by
  haveI : Nonempty (Fin (2*k)) := ⟨⟨0,by omega⟩⟩
  rw [Nat.card_congr (fixedMatchingEventEquiv N M)]
  exact card_fixedComparison _ k (Fintype.card_fin _)

theorem fixedMatchingEvent5_le (N M : Fin 10 → Bool) :
    Nat.card {p : OrientedPairing 5 // FixedPairBad (neighbourRow N p) (neighbourRow M p)} ≤ 432 := by
  rw [card_fixedMatchingEvent 5 (by decide)]
  have h := Arithmetic.M5_le (Fintype.card (ColourClass (incidenceColour (k := 5) N M) Colour.X))
    (Fintype.card (ColourClass (incidenceColour (k := 5) N M) Colour.Y))
    (Fintype.card (ColourClass (incidenceColour (k := 5) N M) Colour.Z))
  norm_num only at ⊢
  omega

#print axioms card_ordinary
#print axioms card_fixedMatchingEvent
#print axioms fixedMatchingEvent5_le

end Crown.MatchingFixedCounts
