import Crown.SmallGraphsSixChecks09
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_080 : ∀ r : Fin 256, ValidCandidate (r.val + 20480) := by decide +kernel
#print axioms six_chunk_080
theorem six_chunk_081 : ∀ r : Fin 256, ValidCandidate (r.val + 20736) := by decide +kernel
#print axioms six_chunk_081
theorem six_chunk_082 : ∀ r : Fin 256, ValidCandidate (r.val + 20992) := by decide +kernel
#print axioms six_chunk_082
theorem six_chunk_083 : ∀ r : Fin 256, ValidCandidate (r.val + 21248) := by decide +kernel
#print axioms six_chunk_083
theorem six_chunk_084 : ∀ r : Fin 256, ValidCandidate (r.val + 21504) := by decide +kernel
#print axioms six_chunk_084
theorem six_chunk_085 : ∀ r : Fin 256, ValidCandidate (r.val + 21760) := by decide +kernel
#print axioms six_chunk_085
theorem six_chunk_086 : ∀ r : Fin 256, ValidCandidate (r.val + 22016) := by decide +kernel
#print axioms six_chunk_086
theorem six_chunk_087 : ∀ r : Fin 256, ValidCandidate (r.val + 22272) := by decide +kernel
#print axioms six_chunk_087
end Crown.SmallGraphs
