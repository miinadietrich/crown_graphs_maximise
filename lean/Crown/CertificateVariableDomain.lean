import Crown.CertificateDimensions
import Mathlib.SetTheory.Cardinal.Finite

namespace Crown.Certificate

def variableOccurs (n : Nat) : Prop :=
  ∃ c : Sat.Clause, List.Mem c pairing8Formula ∧
    ∃ l : Sat.Literal, List.Mem l c ∧ variableIndex l = n

theorem variable_occurs_iff (n : Nat) : variableOccurs n ↔ n < 10116 := by
  constructor
  · rintro ⟨c,hc,l,hl,rfl⟩
    have hh := List.all_eq_true.mp frozen_variables_bounded c hc
    exact of_decide_eq_true (List.all_eq_true.mp hh l hl)
  · intro hn
    refine ⟨(List.range 10116).map Sat.Literal.pos, List.mem_of_head? frozen_first_clause,
      Sat.Literal.pos n, ?_, rfl⟩
    exact List.mem_map.mpr ⟨n,List.mem_range.mpr hn,rfl⟩

theorem frozen_variable_count : Nat.card {n : Nat // variableOccurs n} = 10116 := by
  let e : {n : Nat // variableOccurs n} ≃ Fin 10116 :=
    { toFun := fun n => ⟨n.val,(variable_occurs_iff n.val).mp n.property⟩
      invFun := fun n => ⟨n.val,(variable_occurs_iff n.val).mpr n.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fin]

#print axioms variable_occurs_iff
#print axioms frozen_variable_count
end Crown.Certificate
