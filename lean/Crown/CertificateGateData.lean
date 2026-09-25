import generated.CertificateAssignment
import Crown.CertificateAssembly

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly

theorem assignment_select (s : Fin 256 → Bool) (m : Fin 256) :
    assignment s m.val = s m := by
  simp only [assignment, descriptor, dif_pos m.isLt, value]

theorem assignment_falsum (s : Fin 256 → Bool) : assignment s 256 = false := rfl

theorem assignment_core (s : Fin 256 → Bool) (c : Fin 4935) :
    assignment s (5181+c.val) = value s (.core (cores c)) := by
  have h1 : ¬ 5181+c.val < 256 := by omega
  have h2 : ¬ 5181+c.val = 256 := by omega
  have h3 : ¬ 5181+c.val < 2525 := by omega
  have h4 : ¬ 5181+c.val < 5181 := by omega
  have h5 : 5181+c.val < 10116 := by omega
  simp only [assignment, descriptor, dif_neg h1, if_neg h2, if_neg h3,
    if_neg h4, dif_pos h5, Nat.add_sub_cancel_left]

def templateClause (t : List (Fin 4935)) : Sat.Clause :=
  t.map (fun c => Sat.Literal.pos (5181+c.val))

theorem template_clause_satisfied (s : Fin 256 → Bool) (t : List (Fin 4935))
    (h : ∃ c ∈ t, ∀ m ∈ cores c, s m = true) :
    (valuation (assignment s)).satisfies (templateClause t) := by
  obtain ⟨c, hc, hs⟩ := h
  apply (clause_iff_exists (assignment s) (templateClause t)).mpr
  refine ⟨.pos (5181+c.val), List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
  change assignment s (5181+c.val) = true
  rw [assignment_core]
  exact (core_true_iff s (cores c)).mpr hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allocation_clause_satisfied (s : Fin 256 → Bool) (t : List (Fin 4935))
    (h : ∃ c ∈ t, ∀ m ∈ cores c, s m = true) :
    (valuation (assignment s)).satisfies
      ((List.range 10116).map Sat.Literal.pos) := by
  obtain ⟨c, _, hs⟩ := h
  apply (clause_iff_exists (assignment s) _).mpr
  refine ⟨.pos (5181+c.val), List.mem_map.mpr ⟨5181+c.val, ?_, rfl⟩, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · change assignment s (5181+c.val) = true
    rw [assignment_core]
    exact (core_true_iff s (cores c)).mpr hs

#print axioms assignment_core
#print axioms template_clause_satisfied
#print axioms allocation_clause_satisfied

end Crown.CertificateData
