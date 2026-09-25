import Crown.SmallGraphsSixChecks02
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_024 : ∀ r : Fin 256, ValidCandidate (r.val + 6144) := by decide +kernel
#print axioms six_chunk_024
theorem six_chunk_025 : ∀ r : Fin 256, ValidCandidate (r.val + 6400) := by decide +kernel
#print axioms six_chunk_025
theorem six_chunk_026 : ∀ r : Fin 256, ValidCandidate (r.val + 6656) := by decide +kernel
#print axioms six_chunk_026
theorem six_chunk_027 : ∀ r : Fin 256, ValidCandidate (r.val + 6912) := by decide +kernel
#print axioms six_chunk_027
theorem six_chunk_028 : ∀ r : Fin 256, ValidCandidate (r.val + 7168) := by decide +kernel
#print axioms six_chunk_028
theorem six_chunk_029 : ∀ r : Fin 256, ValidCandidate (r.val + 7424) := by decide +kernel
#print axioms six_chunk_029
theorem six_chunk_030 : ∀ r : Fin 256, ValidCandidate (r.val + 7680) := by decide +kernel
#print axioms six_chunk_030
theorem six_chunk_031 : ∀ r : Fin 256, ValidCandidate (r.val + 7936) := by decide +kernel
#print axioms six_chunk_031
end Crown.SmallGraphs
