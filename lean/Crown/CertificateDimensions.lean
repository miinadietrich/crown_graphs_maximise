import Crown.CertificateDimensionCounts
import Crown.CertificateDimensionBounds
import Crown.CertificateDimensionCover
import Crown.CertificateAssembly

namespace Crown.Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

open Crown.CertificateSemantics Crown.CertificateAssembly

theorem allocation_clause_redundant (a : Nat → Bool)
    (h : (valuation a).satisfies_fmla pairing8Formula.tail) :
    (valuation a).satisfies_fmla pairing8Formula := by
  have hcover := h.prop finalCover finalCover_mem_tail
  have hfirst : (valuation a).satisfies ((List.range 10116).map Sat.Literal.pos) := by
    apply clause_mono a finalCover _ ?_ hcover
    intro l hl
    obtain ⟨n,hn,rfl⟩ := finalCover_positive l hl
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr hn,rfl⟩
  have hf : pairing8Formula =
      ((List.range 10116).map Sat.Literal.pos : Sat.Clause) :: pairing8Formula.tail :=
    List.eq_cons_of_mem_head? frozen_first_clause
  exact hf.symm ▸ (formula_cons_iff (valuation a) _ _).mpr ⟨hfirst, h⟩

#print axioms frozen_clause_count
#print axioms frozen_variables_bounded
#print axioms frozen_first_clause
#print axioms allocation_clause_redundant

end Crown.Certificate
