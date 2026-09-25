import Crown.SmallGraphsSixChecks06
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_056 : ∀ r : Fin 256, ValidCandidate (r.val + 14336) := by decide +kernel
#print axioms six_chunk_056
theorem six_chunk_057 : ∀ r : Fin 256, ValidCandidate (r.val + 14592) := by decide +kernel
#print axioms six_chunk_057
theorem six_chunk_058 : ∀ r : Fin 256, ValidCandidate (r.val + 14848) := by decide +kernel
#print axioms six_chunk_058
theorem six_chunk_059 : ∀ r : Fin 256, ValidCandidate (r.val + 15104) := by decide +kernel
#print axioms six_chunk_059
theorem six_chunk_060 : ∀ r : Fin 256, ValidCandidate (r.val + 15360) := by decide +kernel
#print axioms six_chunk_060
theorem six_chunk_061 : ∀ r : Fin 256, ValidCandidate (r.val + 15616) := by decide +kernel
#print axioms six_chunk_061
theorem six_chunk_062 : ∀ r : Fin 256, ValidCandidate (r.val + 15872) := by decide +kernel
#print axioms six_chunk_062
theorem six_chunk_063 : ∀ r : Fin 256, ValidCandidate (r.val + 16128) := by decide +kernel
#print axioms six_chunk_063
end Crown.SmallGraphs
