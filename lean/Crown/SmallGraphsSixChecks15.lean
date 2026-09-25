import Crown.SmallGraphsSixChecks14
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_120 : ∀ r : Fin 256, ValidCandidate (r.val + 30720) := by decide +kernel
#print axioms six_chunk_120
theorem six_chunk_121 : ∀ r : Fin 256, ValidCandidate (r.val + 30976) := by decide +kernel
#print axioms six_chunk_121
theorem six_chunk_122 : ∀ r : Fin 256, ValidCandidate (r.val + 31232) := by decide +kernel
#print axioms six_chunk_122
theorem six_chunk_123 : ∀ r : Fin 256, ValidCandidate (r.val + 31488) := by decide +kernel
#print axioms six_chunk_123
theorem six_chunk_124 : ∀ r : Fin 256, ValidCandidate (r.val + 31744) := by decide +kernel
#print axioms six_chunk_124
theorem six_chunk_125 : ∀ r : Fin 256, ValidCandidate (r.val + 32000) := by decide +kernel
#print axioms six_chunk_125
theorem six_chunk_126 : ∀ r : Fin 256, ValidCandidate (r.val + 32256) := by decide +kernel
#print axioms six_chunk_126
theorem six_chunk_127 : ∀ r : Fin 256, ValidCandidate (r.val + 32512) := by decide +kernel
#print axioms six_chunk_127
end Crown.SmallGraphs
