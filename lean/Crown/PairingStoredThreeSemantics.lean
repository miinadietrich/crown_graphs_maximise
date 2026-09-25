import generated.PairingStored3
import Crown.PairingCertificateConvention

namespace Crown.PairingStored3
set_option backward.isDefEq.respectTransparency false
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.PairingCoverage Crown.Ranks

/-- The actual60 stored representatives cover all oriented three-pair tests. -/
theorem allPairingsBad_iff_stored {V : Type} (masks : V → Fin 64) :
    Crown.CertificateSixSemantics.AllPairingsBad masks ↔ ∀ t : Fin 60,
      ¬Feasible (fun v => rowOfMask (Crown.CertificateSixSemantics.pairsOfEquiv (stored t))
        (Crown.CertificateSixSemantics.maskBits (masks v))) := by
  have hrows (p : Crown.CertificateSixSemantics.Pairing6) :
      rankRows p (fun v => Crown.CertificateSixSemantics.maskBits (masks v)) =
        fun v => rowOfMask (Crown.CertificateSixSemantics.pairsOfEquiv p)
          (Crown.CertificateSixSemantics.maskBits (masks v)) := by
    rw [rankRows_eq_certificate]
    rfl
  constructor
  · intro h t
    exact h (stored t)
  · intro h p hp
    have hall := (all_bad_iff (fun v => Crown.CertificateSixSemantics.maskBits (masks v))).mpr (by
      intro t ht
      apply h t
      rw [←hrows]
      exact ht)
    exact hall p (by rw [hrows]; exact hp)

#print axioms allPairingsBad_iff_stored
end Crown.PairingStored3
