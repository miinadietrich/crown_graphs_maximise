import Crown.ProbabilitySpecification

namespace Crown.ProbabilitySpecification
open Crown.Matchings
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem prescribed_pair_probability (k : ℕ) (hk : 1 ≤ k) (a b : Fin (2*k)) (hab : a ≠ b) :
    (Nat.card {p : PairingOn (Fin (2*k)) // DirectedPair p a b ∨ DirectedPair p b a} : ℚ) /
      Crown.Arithmetic.Q k = 1 / (2*k-1 : ℚ) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.card_eq_fintype_card,card_unorientedPair_any m (Fintype.card_fin _) a b hab]
  push_cast
  convert prescribedPair_probability m using 1 <;> congr 1 <;> push_cast <;> ring

private theorem residual_firstSet_iff {V : Type*} [DecidableEq V]
    (p : PairingOn V) (a b : V) (hab : a ≠ b) (S : Finset V) (ha : a ∉ S) (hb : b ∉ S) :
    (DirectedPair p a b ∧ ResidualFirstSet p a b S) ↔
      p.1 = insert a S ∧ DirectedPair p a b := by
  constructor
  · rintro ⟨hd,hr⟩
    refine ⟨?_,hd⟩
    ext v
    by_cases hva : v = a
    · subst v
      simp [hd.1]
    by_cases hvb : v = b
    · subst v
      simp [hd.2.1,hva,hb]
    · simpa [hva,hvb] using (hr v).symm
  · rintro ⟨hs,hd⟩
    refine ⟨hd,?_⟩
    intro v
    rw [hs]
    by_cases hva : v = a
    · subst v
      simp [ha]
    by_cases hvb : v = b
    · subst v
      simp [hb]
    · simp [hva,hvb]

theorem residual_fiber (k : ℕ) (a b : Fin (2*(k+1))) (hab : a ≠ b)
    (S : Finset (Fin (2*(k+1)))) (ha : a ∉ S) (hb : b ∉ S) (hS : S.card = k) :
    Nat.card {p : PairingOn (Fin (2*(k+1))) //
      DirectedPair p a b ∧ ResidualFirstSet p a b S} = k.factorial := by
  let s : FirstSets (k+1) := ⟨insert a S,by simp [Finset.card_insert_of_notMem ha,hS]⟩
  have ha' : a ∈ s.val := by simp [s]
  have hb' : b ∉ s.val := by simp [s,Ne.symm hab,hb]
  let e := Equiv.subtypeEquiv (constrainedEquiv (k+1))
    (p := fun p => p.1 = s ∧ DirectedPair (constrainedEquiv (k+1) p) a b)
    (q := fun p => DirectedPair p a b ∧ ResidualFirstSet p a b S)
    (by
      intro p
      rw [residual_firstSet_iff _ a b hab S ha hb]
      constructor
      · rintro ⟨hs,hd⟩
        exact ⟨congrArg Subtype.val hs,hd⟩
      · rintro ⟨hs,hd⟩
        exact ⟨Subtype.ext hs,hd⟩)
  rw [← Nat.card_congr e]
  simpa using Crown.MatchingFirstSetCounts.card_firstSetPair s ⟨a,ha'⟩ ⟨b,hb'⟩

#print axioms prescribed_pair_probability
#print axioms residual_fiber
end Crown.ProbabilitySpecification
