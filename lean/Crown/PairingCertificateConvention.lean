import Crown.PairingCoverage
import Crown.CertificateSemantics

namespace Crown.PairingCoverage

/-- The coordinate incidence convention is exactly the certificate convention. -/
theorem rankRows_eq_certificate {k : ℕ} {V : Type}
    (p : Crown.PairingCoordinates.Coordinates k) (N : V → Fin (2*k) → Bool) :
    rankRows p N = fun v => Crown.CertificateSemantics.rowOfMask
      (fun i => (p (i,false),p (i,true))) (N v) := by
  funext v i
  change Crown.Orientations.entry (N v (p (i,false)),N v (p (i,true))) false =
    Crown.CertificateSemantics.rankOfBits (N v (p (i,false))) (N v (p (i,true)))
  cases N v (p (i,false)) <;> cases N v (p (i,true)) <;> rfl

#print axioms rankRows_eq_certificate
end Crown.PairingCoverage
