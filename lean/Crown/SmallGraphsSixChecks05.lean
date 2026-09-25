import Crown.SmallGraphsSixChecks04
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_040 : ∀ r : Fin 256, ValidCandidate (r.val + 10240) := by decide +kernel
#print axioms six_chunk_040
theorem six_chunk_041 : ∀ r : Fin 256, ValidCandidate (r.val + 10496) := by decide +kernel
#print axioms six_chunk_041
theorem six_chunk_042 : ∀ r : Fin 256, ValidCandidate (r.val + 10752) := by decide +kernel
#print axioms six_chunk_042
theorem six_chunk_043 : ∀ r : Fin 256, ValidCandidate (r.val + 11008) := by decide +kernel
#print axioms six_chunk_043
theorem six_chunk_044 : ∀ r : Fin 256, ValidCandidate (r.val + 11264) := by decide +kernel
#print axioms six_chunk_044
theorem six_chunk_045 : ∀ r : Fin 256, ValidCandidate (r.val + 11520) := by decide +kernel
#print axioms six_chunk_045
theorem six_chunk_046 : ∀ r : Fin 256, ValidCandidate (r.val + 11776) := by decide +kernel
#print axioms six_chunk_046
theorem six_chunk_047 : ∀ r : Fin 256, ValidCandidate (r.val + 12032) := by decide +kernel
#print axioms six_chunk_047
end Crown.SmallGraphs
