import generated.CertificateSixChunk0000
import generated.CertificateChunk0000
import Specification.CertificateDefinitions
import Mathlib.SetTheory.Cardinal.Finite

namespace Crown.Certificate
open Crown.CertificateSemantics
def variableIndex : Sat.Literal → Nat
  | .pos n => n
  | .neg n => n

def finalCover : List Sat.Literal := [.pos 10107, .pos 10113, .pos 10114, .pos 8756, .pos 8775, .pos 8776, .pos 7178, .pos 7212, .pos 7213, .pos 7196, .pos 7214, .pos 7215, .pos 6742, .pos 6743, .pos 7199, .pos 6744, .pos 6745, .pos 7181, .pos 6746, .pos 6747, .pos 8759, .pos 6748, .pos 6749, .pos 6750, .pos 6751, .pos 6752, .pos 6753, .pos 6754, .pos 6755, .pos 6756, .pos 6757, .pos 6761, .pos 8400, .pos 6762, .pos 7811, .pos 6763, .pos 7663, .pos 8777, .pos 8762, .pos 6764, .pos 8079, .pos 6769, .pos 6770, .pos 5446, .pos 5447, .pos 7216, .pos 7184, .pos 6035, .pos 6036, .pos 5451, .pos 5452, .pos 6772, .pos 9134, .pos 5454, .pos 9388, .pos 6773, .pos 6774, .pos 7217, .pos 7202, .pos 5644, .pos 5645, .pos 6251, .pos 6252, .pos 5649, .pos 5650, .pos 6776, .pos 8406, .pos 5652, .pos 8525, .pos 6777, .pos 6778, .pos 6779, .pos 6780, .pos 10110, .pos 10115, .pos 10112, .pos 6781, .pos 9706, .pos 6783, .pos 6784, .pos 6785, .pos 6786, .pos 6787, .pos 6788, .pos 6789, .pos 6790, .pos 6795, .pos 6796, .pos 5477, .pos 5478, .pos 6798, .pos 6799, .pos 5675, .pos 5676, .pos 6801, .pos 6802, .pos 7032, .pos 6057, .pos 6273, .pos 8163, .pos 7035, .pos 8526, .pos 7353, .pos 9389, .pos 9728]

def variableOccurs (n : Nat) : Prop :=
  ∃ c : Sat.Clause, List.Mem c pairing8Formula ∧
    ∃ l : Sat.Literal, List.Mem l c ∧ variableIndex l = n

theorem variable_occurs_iff (n : Nat) : variableOccurs n ↔ n < 10116 := by
  sorry

theorem frozen_variable_count : Nat.card {n : Nat // variableOccurs n} = 10116 := by
  sorry

theorem frozen_clause_count : pairing8Formula.length = 38240 := by
  sorry

theorem frozen_variables_bounded :
    pairing8Formula.all (fun c => (c : List Sat.Literal).all
      (fun l => decide (variableIndex l < 10116))) = true := by
  sorry

theorem frozen_first_clause : pairing8Formula.head? =
    some ((List.range 10116).map Sat.Literal.pos : Sat.Clause) := by
  sorry

theorem allocation_clause_redundant (a : Nat → Bool)
    (h : (valuation a).satisfies_fmla pairing8Formula.tail) :
    (valuation a).satisfies_fmla pairing8Formula := by
  sorry

theorem pairing8Refutation : Sat.Fmla.proof pairing8Formula Sat.Clause.nil := by
  sorry

theorem pairing8_unsatisfiable (v : Sat.Valuation) :
    Not (v.satisfies_fmla pairing8Formula) := by
  sorry

end Crown.Certificate

namespace Crown.CertificateSix

theorem pairing6Refutation : Sat.Fmla.proof pairing6Formula Sat.Clause.nil := by
  sorry

theorem pairing6_unsatisfiable (v : Sat.Valuation) :
    Not (v.satisfies_fmla pairing6Formula) := by
  sorry

end Crown.CertificateSix
