import Crown.CertificateDimensionData

namespace Crown.Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem finalCover_mem_tail : (finalCover : Sat.Clause) ∈ pairing8Formula.tail := by
  exact List.mem_of_getLast? (show pairing8Formula.tail.getLast? =
    some (finalCover : Sat.Clause) from rfl)

theorem finalCover_positive : ∀ l ∈ finalCover,
    ∃ n, n < 10116 ∧ l = Sat.Literal.pos n := by
  intro l hl
  simp only [finalCover, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, ?_, rfl⟩
  all_goals decide

#print axioms finalCover_mem_tail
#print axioms finalCover_positive

end Crown.Certificate
