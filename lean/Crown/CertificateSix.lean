import generated.CertificateSixChunk0133

namespace Crown.CertificateSix

theorem pairing6Refutation : Sat.Fmla.proof pairing6Formula Sat.Clause.nil :=
  step_145231

theorem pairing6_unsatisfiable (v : Sat.Valuation) :
    Not (v.satisfies_fmla pairing6Formula) := pairing6Refutation v

#print axioms pairing6Refutation
#print axioms pairing6_unsatisfiable
end Crown.CertificateSix
