import Crown.Matchings

namespace Crown.MatchingFirstSetCounts
open Crown.Matchings
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def firstSetPairEquiv {k : ℕ} (s : FirstSets k) (a : First s) (b : Second s) :
    {p : OrientedPairing k // p.1 = s ∧ DirectedPair (constrainedEquiv k p) a.val b.val} ≃
    {e : First s ≃ Second s // e a = b} where
  toFun p := by
    rcases p with ⟨⟨t,e⟩,ht,hpair⟩
    cases ht
    exact ⟨e,hpair.2.2 a.property b.property⟩
  invFun e := ⟨⟨s,e.val⟩,rfl,a.property,b.property,fun _ _ => e.property⟩
  left_inv p := by
    rcases p with ⟨⟨t,e⟩,ht,hpair⟩
    cases ht
    rfl
  right_inv _ := rfl

theorem card_firstSetPair {k : ℕ} (s : FirstSets k) (a : First s) (b : Second s) :
    Nat.card {p : OrientedPairing k // p.1 = s ∧ DirectedPair (constrainedEquiv k p) a.val b.val} =
      (k-1).factorial := by
  rw [Nat.card_congr (firstSetPairEquiv s a b),Nat.card_eq_fintype_card,
    card_fixedFirstSet_prescribedPair]

theorem card_firstSetPair_le {k : ℕ} (S : Finset (Fin (2*k))) (a b : Fin (2*k)) :
    Nat.card {p : OrientedPairing k // p.1.val = S ∧ DirectedPair (constrainedEquiv k p) a b} ≤
      (k-1).factorial := by
  by_cases he : Nonempty {p : OrientedPairing k // p.1.val = S ∧ DirectedPair (constrainedEquiv k p) a b}
  · obtain ⟨p⟩ := he
    let s := p.val.1
    have hS : s.val = S := p.property.1
    have ha : a ∈ s.val := p.property.2.1
    have hb : b ∉ s.val := p.property.2.2.1
    let e : {p : OrientedPairing k // p.1.val = S ∧ DirectedPair (constrainedEquiv k p) a b} ≃
        {p : OrientedPairing k // p.1 = s ∧ DirectedPair (constrainedEquiv k p) a b} :=
      Equiv.subtypeEquivProp (by
        funext q
        apply propext
        constructor
        · intro h
          exact ⟨Subtype.ext (h.1.trans hS.symm),h.2⟩
        · intro h
          exact ⟨(congrArg Subtype.val h.1).trans hS,h.2⟩)
    rw [Nat.card_congr e]
    exact (card_firstSetPair s ⟨a,ha⟩ ⟨b,hb⟩).le
  · haveI : IsEmpty {p : OrientedPairing k // p.1.val = S ∧ DirectedPair (constrainedEquiv k p) a b} :=
      not_nonempty_iff.mp he
    simp

#print axioms card_firstSetPair
#print axioms card_firstSetPair_le

end Crown.MatchingFirstSetCounts
