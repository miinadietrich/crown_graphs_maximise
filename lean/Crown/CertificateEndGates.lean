import Crown.CertificateGateData

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly

theorem falsum_clause (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [Sat.Literal.neg 256] := by
  apply (clause_iff_exists _ _).mpr
  exact ⟨.neg 256, List.Mem.head _, rfl⟩

theorem final_count_clause (s : Fin 256 → Bool)
    (h : Fintype.card {m // s m = true} ≤ 8) :
    (valuation (assignment s)).satisfies [Sat.Literal.neg 2524] := by
  apply (clause_iff_exists _ _).mpr
  refine ⟨.neg 2524, List.Mem.head _, ?_⟩
  change Bool.not (value s (.count 256 9)) = true
  rw [(count_final s).mpr h]
  rfl

#print axioms falsum_clause
#print axioms final_count_clause

end Crown.CertificateData
