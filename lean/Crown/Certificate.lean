import generated.CertificateChunk0069

namespace Crown.Certificate

theorem pairing8Refutation : Sat.Fmla.proof pairing8Formula Sat.Clause.nil :=
  step_72722

theorem pairing8_unsatisfiable (v : Sat.Valuation) :
    Not (v.satisfies_fmla pairing8Formula) :=
  pairing8Refutation v

#print axioms pairing8Refutation
#print axioms pairing8_unsatisfiable

end Crown.Certificate
