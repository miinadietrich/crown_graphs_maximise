import Crown.SmallGraphsSixChecks03
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_032 : ∀ r : Fin 256, ValidCandidate (r.val + 8192) := by decide +kernel
#print axioms six_chunk_032
theorem six_chunk_033 : ∀ r : Fin 256, ValidCandidate (r.val + 8448) := by decide +kernel
#print axioms six_chunk_033
theorem six_chunk_034 : ∀ r : Fin 256, ValidCandidate (r.val + 8704) := by decide +kernel
#print axioms six_chunk_034
theorem six_chunk_035 : ∀ r : Fin 256, ValidCandidate (r.val + 8960) := by decide +kernel
#print axioms six_chunk_035
theorem six_chunk_036 : ∀ r : Fin 256, ValidCandidate (r.val + 9216) := by decide +kernel
#print axioms six_chunk_036
theorem six_chunk_037 : ∀ r : Fin 256, ValidCandidate (r.val + 9472) := by decide +kernel
#print axioms six_chunk_037
theorem six_chunk_038 : ∀ r : Fin 256, ValidCandidate (r.val + 9728) := by decide +kernel
#print axioms six_chunk_038
theorem six_chunk_039 : ∀ r : Fin 256, ValidCandidate (r.val + 9984) := by decide +kernel
#print axioms six_chunk_039
end Crown.SmallGraphs
