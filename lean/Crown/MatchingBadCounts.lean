import Crown.MatchingRanks

/-! Counts for the union of the two strict comparison directions. -/

namespace Crown.MatchingBadCounts

open Crown.Matchings Crown.MatchingProbabilities Crown.PairTypes
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V]

theorem colour_classes_card [Fintype V] (col : V → Colour) :
    Fintype.card (ColourClass col Colour.X) + Fintype.card (ColourClass col Colour.Y) +
      Fintype.card (ColourClass col Colour.Z) + Fintype.card (ColourClass col Colour.T) =
      Fintype.card V := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv col)
  rw [Fintype.card_sigma] at h
  change (∑ c ∈ ({Colour.X,Colour.Y,Colour.Z,Colour.T} : Finset Colour),
    Fintype.card (ColourClass col c)) = Fintype.card V at h
  simpa [Nat.add_assoc] using h

def swapColour : Colour → Colour
  | .X => .Y
  | .Y => .X
  | .Z => .Z
  | .T => .T

theorem swapColour_involutive : ∀ c, swapColour (swapColour c) = c := by decide +kernel

theorem swapColour_eq_iff : ∀ a b, swapColour a = b ↔ a = swapColour b := by decide +kernel

theorem allowed_swap_disjoint : ∀ a b, Allowed a b → ¬ Allowed (swapColour a) (swapColour b) := by
  decide +kernel

noncomputable def colourClassSwapEquiv (col : V → Colour) (c : Colour) :
    ColourClass (fun v => swapColour (col v)) c ≃ ColourClass col (swapColour c) :=
  Equiv.subtypeEquivProp (by funext v; exact propext (swapColour_eq_iff (col v) c))

@[simp] theorem card_colourClass_swap [Fintype V] (col : V → Colour) (c : Colour) :
    Fintype.card (ColourClass (fun v => swapColour (col v)) c) =
      Fintype.card (ColourClass col (swapColour c)) :=
  Fintype.card_congr (colourClassSwapEquiv col c)

def BadComparison (col : V → Colour) (p : PairingOn V) : Prop :=
  Comparison col p ∨ Comparison (fun v => swapColour (col v)) p

theorem comparison_swap_disjoint [Nonempty V] (col : V → Colour) (p : PairingOn V) :
    ¬ (Comparison col p ∧ Comparison (fun v => swapColour (col v)) p) := by
  rintro ⟨h,h'⟩
  obtain ⟨a,b,hab,_⟩ := vertex_incident p (Classical.choice (inferInstance : Nonempty V))
  exact allowed_swap_disjoint _ _ (h.1 a b hab) (h'.1 a b hab)

theorem card_badComparison [Fintype V] [Nonempty V] (col : V → Colour) :
    Nat.card {p : PairingOn V // BadComparison col p} =
      Nat.card {p : PairingOn V // Comparison col p} +
      Nat.card {p : PairingOn V // Comparison (fun v => swapColour (col v)) p} := by
  unfold BadComparison
  rw [Nat.card_congr (subtypeOrEquiv _ _ (show Disjoint (fun p : PairingOn V => Comparison col p)
      (fun p => Comparison (fun v => swapColour (col v)) p) from by
    intro q h h' p hp
    exact comparison_swap_disjoint col p ⟨h p hp,h' p hp⟩)), Nat.card_sum]

theorem card_badComparison_noT [Fintype V] (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // BadComparison col p} =
      Arithmetic.P (k+1) (Fintype.card (ColourClass col Colour.X))
        (Fintype.card (ColourClass col Colour.Y)) (Fintype.card (ColourClass col Colour.Z)) 0 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have ht' : ∀ v, swapColour (col v) ≠ Colour.T := by
    intro v hv
    exact ht v ((swapColour_eq_iff _ _).mp hv)
  rw [card_badComparison,card_comparison_noT col ht k hcard,
    card_comparison_noT (fun v => swapColour (col v)) ht' k hcard]
  simp only [card_colourClass_swap]
  simp only [swapColour]
  rw [Arithmetic.M_swap_xy ((k+1 : ℕ) : ℤ)
    (Fintype.card (ColourClass col Colour.Y) : ℤ) (Fintype.card (ColourClass col Colour.X) : ℤ)
    (Fintype.card (ColourClass col Colour.Z) : ℤ)]
  rw [Arithmetic.M_swap_xy (k : ℤ) (Fintype.card (ColourClass col Colour.Y) : ℤ)
    ((Fintype.card (ColourClass col Colour.X) : ℤ)-2) (Fintype.card (ColourClass col Colour.Z) : ℤ)]
  simp only [Arithmetic.P,if_true,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  omega

theorem card_badComparison_oneT [Fintype V] (col : V → Colour) (t : V) (ht : col t = Colour.T)
    (hunique : ∀ v, col v = Colour.T → v = t)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // BadComparison col p} =
      Arithmetic.P (k+1) (Fintype.card (ColourClass col Colour.X))
        (Fintype.card (ColourClass col Colour.Y)) (Fintype.card (ColourClass col Colour.Z)) 1 := by
  haveI : Nonempty V := ⟨t⟩
  have ht' : swapColour (col t) = Colour.T := by simp [ht,swapColour]
  have hu' : ∀ v, swapColour (col v) = Colour.T → v = t := by
    intro v hv
    exact hunique v ((swapColour_eq_iff _ _).mp hv)
  rw [card_badComparison,card_comparison_oneT col t ht hunique k hcard,
    card_comparison_oneT (fun v => swapColour (col v)) t ht' hu' k hcard]
  simp only [card_colourClass_swap]
  simp only [swapColour]
  rw [Arithmetic.M_swap_xy (k : ℤ) (Fintype.card (ColourClass col Colour.Y) : ℤ)
    ((Fintype.card (ColourClass col Colour.X) : ℤ)-1) (Fintype.card (ColourClass col Colour.Z) : ℤ)]
  simp [Arithmetic.P,Nat.cast_add]

theorem card_badComparison_multipleT [Fintype V] (col : V → Colour)
    (v w : V) (hv : col v = Colour.T) (hw : col w = Colour.T) (hne : v ≠ w) :
    Nat.card {p : PairingOn V // BadComparison col p} = 0 := by
  haveI : Nonempty V := ⟨v⟩
  rw [card_badComparison,card_comparison_multipleT col v w hv hw hne,
    card_comparison_multipleT (fun v => swapColour (col v)) v w (by simp [hv,swapColour])
      (by simp [hw,swapColour]) hne]

theorem card_badComparison_eq_P [Fintype V] (col : V → Colour)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // BadComparison col p} =
      Arithmetic.P (k+1) (Fintype.card (ColourClass col Colour.X))
        (Fintype.card (ColourClass col Colour.Y)) (Fintype.card (ColourClass col Colour.Z))
        (Fintype.card (ColourClass col Colour.T)) := by
  by_cases h0 : Fintype.card (ColourClass col Colour.T) = 0
  · have ht : ∀ v, col v ≠ Colour.T := by
      intro v hv
      have hp := Fintype.card_pos_iff.mpr (Nonempty.intro (⟨v,hv⟩ : ColourClass col Colour.T))
      change 0 < Fintype.card (ColourClass col Colour.T) at hp
      omega
    rw [h0]
    exact card_badComparison_noT col ht k hcard
  · by_cases h1 : Fintype.card (ColourClass col Colour.T) = 1
    · obtain ⟨t,ht⟩ := Fintype.card_eq_one_iff.mp h1
      rw [h1]
      exact card_badComparison_oneT col t.val t.property
        (fun v hv => congrArg Subtype.val (ht ⟨v,hv⟩)) k hcard
    · obtain ⟨v,hv⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (ColourClass col Colour.T))
      have hw : ∃ w : ColourClass col Colour.T, w ≠ ⟨v,hv⟩ := by
        by_contra h
        have he : ∀ w : ColourClass col Colour.T, w = ⟨v,hv⟩ := by simpa using h
        exact h1 (Fintype.card_eq_one_iff.mpr ⟨⟨v,hv⟩,he⟩)
      obtain ⟨w,hw⟩ := hw
      rw [card_badComparison_multipleT col w.val v w.property hv
        (fun he => hw (Subtype.ext he)),Arithmetic.P_eq_zero_of_two_le_t (by omega)]

theorem swap_colourOfBits : ∀ a b : Bool, swapColour (colourOfBits (a,b)) = colourOfBits (b,a) := by
  decide +kernel

theorem swap_incidenceColour {k : ℕ} (N M : Fin (2*k) → Bool) :
    (fun v => swapColour (MatchingRanks.incidenceColour N M v)) =
      MatchingRanks.incidenceColour M N := by
  funext v
  exact swap_colourOfBits (N v) (M v)

theorem pairBad_iff_badComparison {k : ℕ} (N M : Fin (2*k) → Bool) (p : OrientedPairing k) :
    Crown.Orientations.PairBad (MatchingRanks.neighbourRow N p) (MatchingRanks.neighbourRow M p)
      (fun _ => false) ↔ BadComparison (MatchingRanks.incidenceColour N M) (constrainedEquiv k p) := by
  rw [MatchingRanks.pairBad_iff_comparison,BadComparison,swap_incidenceColour]

noncomputable def badMatchingEventEquiv {k : ℕ} (N M : Fin (2*k) → Bool) :
    {p : OrientedPairing k // Crown.Orientations.PairBad (MatchingRanks.neighbourRow N p)
      (MatchingRanks.neighbourRow M p) (fun _ => false)} ≃
    {p : PairingOn (Fin (2*k)) // BadComparison (MatchingRanks.incidenceColour N M) p} :=
  Equiv.subtypeEquiv (constrainedEquiv k) (by intro p; exact pairBad_iff_badComparison N M p)

theorem card_badMatchingEvent (k : ℕ) (N M : Fin (2*(k+1)) → Bool) :
    Nat.card {p : OrientedPairing (k+1) // Crown.Orientations.PairBad (MatchingRanks.neighbourRow N p)
      (MatchingRanks.neighbourRow M p) (fun _ => false)} =
      Arithmetic.P (k+1) (Fintype.card (ColourClass (MatchingRanks.incidenceColour N M) Colour.X))
        (Fintype.card (ColourClass (MatchingRanks.incidenceColour N M) Colour.Y))
        (Fintype.card (ColourClass (MatchingRanks.incidenceColour N M) Colour.Z))
        (Fintype.card (ColourClass (MatchingRanks.incidenceColour N M) Colour.T)) := by
  rw [Nat.card_congr (badMatchingEventEquiv N M)]
  exact card_badComparison_eq_P _ k (Fintype.card_fin _)

#print axioms card_badComparison_eq_P
#print axioms card_badMatchingEvent

end Crown.MatchingBadCounts
