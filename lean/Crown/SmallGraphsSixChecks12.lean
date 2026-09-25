import Crown.SmallGraphsSixChecks11
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_096 : ∀ r : Fin 256, ValidCandidate (r.val + 24576) := by decide +kernel
#print axioms six_chunk_096
theorem six_chunk_097 : ∀ r : Fin 256, ValidCandidate (r.val + 24832) := by decide +kernel
#print axioms six_chunk_097
theorem six_chunk_098 : ∀ r : Fin 256, ValidCandidate (r.val + 25088) := by decide +kernel
#print axioms six_chunk_098
theorem six_chunk_099 : ∀ r : Fin 256, ValidCandidate (r.val + 25344) := by decide +kernel
#print axioms six_chunk_099
theorem six_chunk_100 : ∀ r : Fin 256, ValidCandidate (r.val + 25600) := by decide +kernel
#print axioms six_chunk_100
theorem six_chunk_101 : ∀ r : Fin 256, ValidCandidate (r.val + 25856) := by decide +kernel
#print axioms six_chunk_101
theorem six_chunk_102 : ∀ r : Fin 256, ValidCandidate (r.val + 26112) := by decide +kernel
#print axioms six_chunk_102
theorem six_chunk_103 : ∀ r : Fin 256, ValidCandidate (r.val + 26368) := by decide +kernel
#print axioms six_chunk_103
end Crown.SmallGraphs
