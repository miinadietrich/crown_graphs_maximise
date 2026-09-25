import Crown.Matchings

/-! Anchored oriented unordered matchings. The first endpoint of the pair
containing a distinguished vertex is fixed to be that vertex. Counting uses
Mathlib's subset-containing-subset formula, not enumeration of permutations. -/

namespace Crown.MatchingRepresentatives
open Crown.Matchings
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false

abbrev AnchoredFirstSets (k : ℕ) (v : Fin (2*k)) := {s : FirstSets k // v ∈ s.val}
abbrev AnchoredPairing (k : ℕ) (v : Fin (2*k)) := {p : OrientedPairing k // v ∈ p.1.val}

noncomputable def anchoredFirstEquiv {k : ℕ} (v : Fin (2*k)) :
    AnchoredFirstSets k v ≃
      {s : Finset (Fin (2*k)) // s ∈ (Finset.univ.powersetCard k).filter ({v} ⊆ ·)} where
  toFun s := ⟨s.val.val,Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,s.val.property⟩,
      Finset.singleton_subset_iff.mpr s.property⟩⟩
  invFun s := ⟨⟨s.val,(Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.property).1).2⟩,
    Finset.singleton_subset_iff.mp (Finset.mem_filter.mp s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_anchoredFirstSets {k : ℕ} (v : Fin (2*k)) :
    Fintype.card (AnchoredFirstSets k v) = Nat.choose (2*k-1) (k-1) := by
  rw [Fintype.card_congr (anchoredFirstEquiv v),Fintype.card_coe]
  have hk : 1 ≤ k := by have hv := v.isLt; omega
  rw [Finset.card_filter_powersetCard_subset {v} Finset.univ k
    (Finset.subset_univ _) (by simpa using hk)]
  simp

noncomputable def anchoredPairingEquiv {k : ℕ} (v : Fin (2*k)) :
    AnchoredPairing k v ≃ (Σ s : AnchoredFirstSets k v, First s.val ≃ Second s.val) where
  toFun p := ⟨⟨p.val.1,p.property⟩,p.val.2⟩
  invFun p := ⟨⟨p.1.val,p.2⟩,p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_anchoredPairing {k : ℕ} (v : Fin (2*k)) :
    Fintype.card (AnchoredPairing k v) = Nat.choose (2*k-1) (k-1) * k.factorial := by
  rw [Fintype.card_congr (anchoredPairingEquiv v),Fintype.card_sigma]
  simp_rw [card_pairing_fiber]
  simp [card_anchoredFirstSets]

theorem card_anchoredPairing3 : Fintype.card (AnchoredPairing 3 0) = 60 := by
  rw [card_anchoredPairing]
  norm_num [Nat.choose,Nat.factorial]

theorem card_anchoredPairing4 : Fintype.card (AnchoredPairing 4 0) = 840 := by
  rw [card_anchoredPairing]
  norm_num [Nat.choose,Nat.factorial]

#print axioms card_anchoredFirstSets
#print axioms card_anchoredPairing
#print axioms card_anchoredPairing3
#print axioms card_anchoredPairing4

end Crown.MatchingRepresentatives
