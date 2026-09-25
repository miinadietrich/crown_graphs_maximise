import Crown.SmallGraphsSixChecks13
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_112 : ∀ r : Fin 256, ValidCandidate (r.val + 28672) := by decide +kernel
#print axioms six_chunk_112
theorem six_chunk_113 : ∀ r : Fin 256, ValidCandidate (r.val + 28928) := by decide +kernel
#print axioms six_chunk_113
theorem six_chunk_114 : ∀ r : Fin 256, ValidCandidate (r.val + 29184) := by decide +kernel
#print axioms six_chunk_114
theorem six_chunk_115 : ∀ r : Fin 256, ValidCandidate (r.val + 29440) := by decide +kernel
#print axioms six_chunk_115
theorem six_chunk_116 : ∀ r : Fin 256, ValidCandidate (r.val + 29696) := by decide +kernel
#print axioms six_chunk_116
theorem six_chunk_117 : ∀ r : Fin 256, ValidCandidate (r.val + 29952) := by decide +kernel
#print axioms six_chunk_117
theorem six_chunk_118 : ∀ r : Fin 256, ValidCandidate (r.val + 30208) := by decide +kernel
#print axioms six_chunk_118
theorem six_chunk_119 : ∀ r : Fin 256, ValidCandidate (r.val + 30464) := by decide +kernel
#print axioms six_chunk_119
end Crown.SmallGraphs
