import Crown.CertificateSixGateData

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly

theorem falsum_clause (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [Sat.Literal.neg 64] := by
  apply (clause_iff_exists _ _).mpr
  exact ⟨.neg 64, List.Mem.head _, rfl⟩

theorem final_count_clause (s : Fin 64 → Bool)
    (h : Fintype.card {m // s m = true} ≤ 6) :
    (valuation (assignment s)).satisfies [Sat.Literal.neg 491] := by
  apply (clause_iff_exists _ _).mpr
  refine ⟨.neg 491, List.Mem.head _, ?_⟩
  change Bool.not (value s (.count 64 7)) = true
  rw [(count_final s).mpr h]
  rfl

#print axioms falsum_clause
#print axioms final_count_clause

end Crown.CertificateSixData
