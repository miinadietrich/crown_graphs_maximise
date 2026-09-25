import Crown.SmallGraphsSixChecks10
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_088 : ∀ r : Fin 256, ValidCandidate (r.val + 22528) := by decide +kernel
#print axioms six_chunk_088
theorem six_chunk_089 : ∀ r : Fin 256, ValidCandidate (r.val + 22784) := by decide +kernel
#print axioms six_chunk_089
theorem six_chunk_090 : ∀ r : Fin 256, ValidCandidate (r.val + 23040) := by decide +kernel
#print axioms six_chunk_090
theorem six_chunk_091 : ∀ r : Fin 256, ValidCandidate (r.val + 23296) := by decide +kernel
#print axioms six_chunk_091
theorem six_chunk_092 : ∀ r : Fin 256, ValidCandidate (r.val + 23552) := by decide +kernel
#print axioms six_chunk_092
theorem six_chunk_093 : ∀ r : Fin 256, ValidCandidate (r.val + 23808) := by decide +kernel
#print axioms six_chunk_093
theorem six_chunk_094 : ∀ r : Fin 256, ValidCandidate (r.val + 24064) := by decide +kernel
#print axioms six_chunk_094
theorem six_chunk_095 : ∀ r : Fin 256, ValidCandidate (r.val + 24320) := by decide +kernel
#print axioms six_chunk_095
end Crown.SmallGraphs
