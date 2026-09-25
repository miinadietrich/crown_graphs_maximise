import Crown.CertificateDimensionData

namespace Crown.Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem frozen_clause_count : pairing8Formula.length = 38240 := by decide +kernel

theorem frozen_first_clause : pairing8Formula.head? =
    some ((List.range 10116).map Sat.Literal.pos : Sat.Clause) := by rfl

#print axioms frozen_clause_count
#print axioms frozen_first_clause

end Crown.Certificate
