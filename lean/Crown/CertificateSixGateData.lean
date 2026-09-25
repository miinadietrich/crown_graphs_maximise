import generated.CertificateSixAssignment
import Crown.CertificateAssembly

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly

theorem assignment_select (s : Fin 64 → Bool) (m : Fin 64) :
    assignment s m.val = s m := by
  simp only [assignment, descriptor, dif_pos m.isLt, value]

theorem assignment_falsum (s : Fin 64 → Bool) : assignment s 64 = false := rfl

theorem assignment_core (s : Fin 64 → Bool) (c : Fin 38430) :
    assignment s (952+c.val) = value s (.core (cores c)) := by
  have h1 : ¬ 952+c.val < 64 := by omega
  have h2 : ¬ 952+c.val = 64 := by omega
  have h3 : ¬ 952+c.val < 492 := by omega
  have h4 : ¬ 952+c.val < 952 := by omega
  have h5 : 952+c.val < 39382 := by omega
  simp only [assignment, descriptor, dif_neg h1, if_neg h2, if_neg h3,
    if_neg h4, dif_pos h5, Nat.add_sub_cancel_left]

def templateClause (t : List (Fin 38430)) : Sat.Clause :=
  t.map (fun c => Sat.Literal.pos (952+c.val))

theorem template_clause_satisfied (s : Fin 64 → Bool) (t : List (Fin 38430))
    (h : ∃ c ∈ t, ∀ m ∈ cores c, s m = true) :
    (valuation (assignment s)).satisfies (templateClause t) := by
  obtain ⟨c, hc, hs⟩ := h
  apply (clause_iff_exists (assignment s) (templateClause t)).mpr
  refine ⟨.pos (952+c.val), List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
  change assignment s (952+c.val) = true
  rw [assignment_core]
  exact (core_true_iff s (cores c)).mpr hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allocation_clause_satisfied (s : Fin 64 → Bool) (t : List (Fin 38430))
    (h : ∃ c ∈ t, ∀ m ∈ cores c, s m = true) :
    (valuation (assignment s)).satisfies
      ((List.range 39382).map Sat.Literal.pos) := by
  obtain ⟨c, _, hs⟩ := h
  apply (clause_iff_exists (assignment s) _).mpr
  refine ⟨.pos (952+c.val), List.mem_map.mpr ⟨952+c.val, ?_, rfl⟩, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · change assignment s (952+c.val) = true
    rw [assignment_core]
    exact (core_true_iff s (cores c)).mpr hs

#print axioms assignment_core
#print axioms template_clause_satisfied
#print axioms allocation_clause_satisfied

end Crown.CertificateSixData
