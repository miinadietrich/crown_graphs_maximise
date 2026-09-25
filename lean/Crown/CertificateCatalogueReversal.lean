import Crown.CertificateCatalogueConverse
import Crown.PairingCoverage

/-! Minimal neighbourhood obstructions depend on an oriented pairing only up
to coordinate order and simultaneous reversal. -/
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.PairingCoordinates Crown.PairingCoverage
open Crown.MatchingReversal

def pairingRows (p : Pairing8) : Fin 256 → RankRow :=
  fun m => rowOfMask (pairsOfEquiv p) (maskBits m)

theorem pairingRows_eq_rankRows (p : Pairing8) :
    pairingRows p = rankRows p maskBits := by
  funext m i
  change rankOfBits (maskBits m (p (i,false))) (maskBits m (p (i,true))) =
    Crown.Orientations.entry (maskBits m (p (i,false)),maskBits m (p (i,true))) false
  cases maskBits m (p (i,false)) <;> cases maskBits m (p (i,true)) <;> rfl

theorem minimalMask_congr (rows rows' : Fin 256 → RankRow)
    (h : ∀ M, maskFeasible rows M ↔ maskFeasible rows' M)
    (M : Finset (Fin 256)) :
    MinimalMaskFamily rows M ↔ MinimalMaskFamily rows' M := by
  simp only [MinimalMaskFamily, h]

theorem maskFeasible_pairing_eq (p q : Pairing8)
    (h : ofCoordinates p = ofCoordinates q) (M : Finset (Fin 256)) :
    maskFeasible (pairingRows p) M ↔ maskFeasible (pairingRows q) M := by
  simp only [maskFeasible,pairingRows_eq_rankRows]
  exact feasible_of_pairing_eq p q h (fun m : {m // m ∈ M} => maskBits m.val)

theorem maskFeasible_reverse (p : Pairing8) (M : Finset (Fin 256)) :
    maskFeasible (pairingRows (reverseCoordinates p)) M ↔
      maskFeasible (pairingRows p) M := by
  simp only [maskFeasible,pairingRows_eq_rankRows]
  exact feasible_reverse p (fun m : {m // m ∈ M} => maskBits m.val)

theorem minimalMask_pairing_eq (p q : Pairing8)
    (h : ofCoordinates p = ofCoordinates q) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows p) M ↔ MinimalMaskFamily (pairingRows q) M :=
  minimalMask_congr _ _ (maskFeasible_pairing_eq p q h) M

theorem minimalMask_reverse (p : Pairing8) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (reverseCoordinates p)) M ↔
      MinimalMaskFamily (pairingRows p) M :=
  minimalMask_congr _ _ (maskFeasible_reverse p) M

theorem minimalMask_exists_iff_stored {n : ℕ} (family : Fin n → Pairing8)
    (hfamily : ∀ p, ∃ t, ofCoordinates (family t) = ofCoordinates p ∨
      ofCoordinates (family t) = reverseOriented (ofCoordinates p))
    (M : Finset (Fin 256)) :
    (∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M) ↔
      ∃ t, MinimalMaskFamily (pairingRows (family t)) M := by
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨t,ht|ht⟩ := hfamily p
    · exact ⟨t,(minimalMask_pairing_eq _ _ ht M).mpr hp⟩
    · have he : ofCoordinates (family t) = ofCoordinates (reverseCoordinates p) :=
        ht.trans (ofCoordinates_reverse p).symm
      exact ⟨t,(minimalMask_pairing_eq _ _ he M).mpr ((minimalMask_reverse p M).mpr hp)⟩
  · rintro ⟨t,ht⟩
    exact ⟨family t,ht⟩

#print axioms maskFeasible_pairing_eq
#print axioms maskFeasible_reverse
#print axioms minimalMask_exists_iff_stored
end Crown.CertificateData
