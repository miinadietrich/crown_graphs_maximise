import generated.PairingStored4
import Crown.PairingCertificateConvention

namespace Crown.PairingStored4
set_option backward.isDefEq.respectTransparency false
open Crown.CertificateSemantics Crown.PairingCoverage Crown.Ranks

/-- Every oriented pairing is tested by the stored840 representatives, modulo
pair order and simultaneous endpoint reversal, both proved to preserve feasibility. -/
theorem allPairingsBad_iff_stored {V : Type} (masks : V → Fin 256) :
    AllPairingsBad masks ↔ ∀ t : Fin 840,
      ¬Feasible (fun v => rowOfMask (pairsOfEquiv (Crown.CertificateData.pairings t))
        (maskBits (masks v))) := by
  have hrows (p : Pairing8) :
      rankRows p (fun v => maskBits (masks v)) =
        fun v => rowOfMask (pairsOfEquiv p) (maskBits (masks v)) := by
    rw [rankRows_eq_certificate]
    rfl
  constructor
  · intro h t
    exact h (Crown.CertificateData.pairings t)
  · intro h p hp
    have hall := (all_bad_iff (fun v => maskBits (masks v))).mpr (by
      intro t ht
      apply h t
      change Feasible (fun v => rowOfMask (pairsOfEquiv (stored t)) (maskBits (masks v)))
      rw [←hrows]
      exact ht)
    exact hall p (by rw [hrows]; exact hp)

#print axioms allPairingsBad_iff_stored
end Crown.PairingStored4
