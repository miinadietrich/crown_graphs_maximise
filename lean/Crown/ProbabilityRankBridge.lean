import Crown.ProbabilitySpecification

namespace Crown.ProbabilitySpecification
open Crown.Matchings Crown.Ranks Crown.Orientations Crown.PairTypes
open Crown.MatchingProbabilities Crown.MatchingBadCounts
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem comparison_realizes {k : ℕ} (col : Fin (2*k) → Colour)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    Comparison col p ↔
      (∀ i, Allowed (col (e (i,false))) (col (e (i,true)))) ∧
      AtMostOneExceptional (fun i => (col (e (i,false)),col (e (i,true)))) := by
  have hp : ∀ i, DirectedPair p (e (i,false)) (e (i,true)) :=
    fun i => (he _ _).mpr ⟨i,rfl,rfl⟩
  constructor
  · intro h
    refine ⟨fun i => h.1 _ _ (hp i),?_⟩
    intro i j hi hj
    have hij := h.2 _ _ _ _ (hp i) (hp j) hi hj
    exact congrArg Prod.fst (e.injective hij)
  · rintro ⟨hall,huniq⟩
    constructor
    · intro a b hab
      obtain ⟨i,rfl,rfl⟩ := (he a b).mp hab
      exact hall i
    · intro a b c d hab hcd heab hecd
      obtain ⟨i,rfl,rfl⟩ := (he a b).mp hab
      obtain ⟨j,rfl,rfl⟩ := (he c d).mp hcd
      exact congrArg (fun i => e (i,false)) (huniq i j heab hecd)

theorem incidence_realizes {k : ℕ} (N M : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    Comparison (Crown.MatchingRanks.incidenceColour N M) p ↔
      ¬ DoubleStar (neighbourRow N e) ∧ ¬ DoubleStar (neighbourRow M e) ∧
      StrictBelow (zeroRow (neighbourRow N e) (fun _ => false))
        (zeroRow (neighbourRow M e) (fun _ => false)) := by
  let col := Crown.MatchingRanks.incidenceColour N M
  let pc := fun i => (col (e (i,false)),col (e (i,true)))
  have hl : smaller pc = neighbourRow N e := by
    funext i
    simp [smaller,pc,col,Crown.MatchingRanks.incidenceColour,neighbourRow,bits_colourOfBits]
  have hr : larger pc = neighbourRow M e := by
    funext i
    simp [larger,pc,col,Crown.MatchingRanks.incidenceColour,neighbourRow,bits_colourOfBits]
  rw [comparison_realizes _ p e he]
  exact (global_directed_iff pc).symm.trans (by rw [hl,hr])

theorem pairBad_realizes {k : ℕ} (N M : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    PairBad (neighbourRow N e) (neighbourRow M e) (fun _ => false) ↔
      BadComparison (Crown.MatchingRanks.incidenceColour N M) p := by
  rw [BadComparison,Crown.MatchingBadCounts.swap_incidenceColour,
    incidence_realizes N M p e he,incidence_realizes M N p e he]
  unfold PairBad
  tauto

theorem bad_event_iff {k : ℕ} (N M : Fin (2*k) → Bool) (p : PairingOn (Fin (2*k))) :
    BadPairEvent N M p ↔ BadComparison (Crown.MatchingRanks.incidenceColour N M) p := by
  constructor
  · rintro ⟨e,he,hbad⟩
    exact (pairBad_realizes N M p e he).mp hbad
  · intro hbad
    obtain ⟨e,he⟩ := coordinates_exist k p
    exact ⟨e,he,(pairBad_realizes N M p e he).mpr hbad⟩

private theorem colour_x (a b : Bool) : colourOfBits (a,b) = Colour.X ↔ a = true ∧ b = false := by
  cases a <;> cases b <;> decide
private theorem colour_y (a b : Bool) : colourOfBits (a,b) = Colour.Y ↔ a = false ∧ b = true := by
  cases a <;> cases b <;> decide
private theorem colour_z (a b : Bool) : colourOfBits (a,b) = Colour.Z ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide
private theorem colour_t (a b : Bool) : colourOfBits (a,b) = Colour.T ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> decide

private theorem card_colour {V : Type*} [Fintype V] (col : V → Colour) (c : Colour)
    (P : V → Prop) (h : ∀ v, col v = c ↔ P v) :
    Fintype.card (ColourClass col c) = Nat.card {v // P v} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivProp (funext (fun v => propext (h v))))

theorem bad_pair_card (k : ℕ) (hk : 1 ≤ k) (N M : Fin (2*k) → Bool) :
    Nat.card {p : PairingOn (Fin (2*k)) // BadPairEvent N M p} =
      Crown.Arithmetic.P k
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = false})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = false}) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.card_congr (Equiv.subtypeEquivProp (funext (fun p => propext (bad_event_iff N M p))))]
  rw [card_badComparison_eq_P _ m (Fintype.card_fin _)]
  congr 1
  · exact card_colour _ _ _ (fun v => colour_x (N v) (M v))
  · exact card_colour _ _ _ (fun v => colour_y (N v) (M v))
  · exact card_colour _ _ _ (fun v => colour_z (N v) (M v))
  · exact card_colour _ _ _ (fun v => colour_t (N v) (M v))

#print axioms comparison_realizes
#print axioms incidence_realizes
#print axioms bad_event_iff
#print axioms bad_pair_card

theorem ordinary_realizes {k : ℕ} (col : Fin (2*k) → Colour)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    Respects p (ordinaryRelation col) ↔
      ∀ i, Ordinary (col (e (i,false))) (col (e (i,true))) := by
  constructor
  · intro h i
    exact h _ _ ((he _ _).mpr ⟨i,rfl,rfl⟩)
  · intro h a b hab
    obtain ⟨i,rfl,rfl⟩ := (he a b).mp hab
    exact h i

theorem fixed_incidence_realizes {k : ℕ} (N M : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    Respects p (ordinaryRelation (Crown.MatchingRanks.incidenceColour N M)) ↔
      Fixed (rankRow N e) ∧ Fixed (rankRow M e) ∧
      StrictBelow (zeroRow (neighbourRow N e) (fun _ => false))
        (zeroRow (neighbourRow M e) (fun _ => false)) := by
  let col := Crown.MatchingRanks.incidenceColour N M
  let pc := fun i => (col (e (i,false)),col (e (i,true)))
  have hl : smaller pc = neighbourRow N e := by
    funext i
    simp [smaller,pc,col,Crown.MatchingRanks.incidenceColour,neighbourRow,bits_colourOfBits]
  have hr : larger pc = neighbourRow M e := by
    funext i
    simp [larger,pc,col,Crown.MatchingRanks.incidenceColour,neighbourRow,bits_colourOfBits]
  rw [ordinary_realizes _ p e he]
  exact (global_fixed_iff pc).symm.trans (by rw [hl,hr]; rfl)

theorem fixed_realizes {k : ℕ} (N M : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (e : Coordinates k) (he : Realizes p e) :
    Crown.MatchingFixedCounts.FixedPairBad (neighbourRow N e) (neighbourRow M e) ↔
      Crown.MatchingFixedCounts.FixedComparison (Crown.MatchingRanks.incidenceColour N M) p := by
  rw [Crown.MatchingFixedCounts.FixedComparison,Crown.MatchingBadCounts.swap_incidenceColour,
    fixed_incidence_realizes N M p e he,fixed_incidence_realizes M N p e he]
  unfold Crown.MatchingFixedCounts.FixedPairBad rankRow
  tauto

theorem fixed_event_iff {k : ℕ} (N M : Fin (2*k) → Bool) (p : PairingOn (Fin (2*k))) :
    FixedPairEvent N M p ↔
      Crown.MatchingFixedCounts.FixedComparison (Crown.MatchingRanks.incidenceColour N M) p := by
  constructor
  · rintro ⟨e,he,hbad⟩
    exact (fixed_realizes N M p e he).mp hbad
  · intro hbad
    obtain ⟨e,he⟩ := coordinates_exist k p
    exact ⟨e,he,(fixed_realizes N M p e he).mpr hbad⟩

theorem fixed_pair_card (k : ℕ) (hk : 1 ≤ k) (N M : Fin (2*k) → Bool) :
    Nat.card {p : PairingOn (Fin (2*k)) // FixedPairEvent N M p} =
      2 * Crown.Arithmetic.M k
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = false})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = true}) := by
  haveI : NeZero (2*k) := ⟨by omega⟩
  rw [Nat.card_congr (Equiv.subtypeEquivProp (funext (fun p => propext (fixed_event_iff N M p))))]
  rw [Crown.MatchingFixedCounts.card_fixedComparison _ k (Fintype.card_fin _)]
  have hx := card_colour (Crown.MatchingRanks.incidenceColour N M) Colour.X _
    (fun v => colour_x (N v) (M v))
  have hy := card_colour (Crown.MatchingRanks.incidenceColour N M) Colour.Y _
    (fun v => colour_y (N v) (M v))
  have hz := card_colour (Crown.MatchingRanks.incidenceColour N M) Colour.Z _
    (fun v => colour_z (N v) (M v))
  rw [hx,hy,hz]

#print axioms fixed_event_iff
#print axioms fixed_pair_card
end Crown.ProbabilitySpecification
