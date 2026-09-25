import Specification.PairingStoredData

namespace Crown.PairingCoverage
open Crown.PairingCoordinates Crown.Ranks

theorem feasible_reverse {k : ℕ} {V : Type*} (p : Coordinates k)
    (N : V → Fin (2*k) → Bool) :
    Feasible (rankRows (reverseCoordinates p) N) ↔ Feasible (rankRows p N) := by
  sorry
end Crown.PairingCoverage

namespace Crown.MatchingRepresentatives

theorem card_anchoredPairing3 : Fintype.card (AnchoredPairing 3 0) = 60 := by
  sorry

theorem card_anchoredPairing4 : Fintype.card (AnchoredPairing 4 0) = 840 := by
  sorry
end Crown.MatchingRepresentatives

namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.Ranks Crown.CertificateSemantics

theorem coordinates_complete (p : Coordinates 3) :
    ∃ t : Fin 60, ∃ e : Equiv.Perm (Fin 3),
      (∀ i b, stored t (e i,b) = p (i,b)) ∨
      (∀ i b, stored t (e i,b) = p (i,!b)) := by
  sorry

theorem allPairingsBad_iff_stored {V : Type} (masks : V → Fin 64) :
    Crown.CertificateSixSemantics.AllPairingsBad masks ↔ ∀ t : Fin 60,
      ¬Feasible (fun v => rowOfMask (Crown.CertificateSixSemantics.pairsOfEquiv (stored t))
        (Crown.CertificateSixSemantics.maskBits (masks v))) := by
  sorry
end Crown.PairingStored3

namespace Crown.PairingStored4
open Crown.PairingCoordinates Crown.Ranks Crown.CertificateSemantics

theorem coordinates_complete (p : Coordinates 4) :
    ∃ t : Fin 840, ∃ e : Equiv.Perm (Fin 4),
      (∀ i b, stored t (e i,b) = p (i,b)) ∨
      (∀ i b, stored t (e i,b) = p (i,!b)) := by
  sorry

theorem allPairingsBad_iff_stored {V : Type} (masks : V → Fin 256) :
    AllPairingsBad masks ↔ ∀ t : Fin 840,
      ¬Feasible (fun v => rowOfMask (pairsOfEquiv (Crown.CertificateData.pairings t))
        (maskBits (masks v))) := by
  sorry
end Crown.PairingStored4
