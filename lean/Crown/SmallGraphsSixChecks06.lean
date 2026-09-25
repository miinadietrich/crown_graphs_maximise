import Crown.SmallGraphsSixChecks05
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_048 : ∀ r : Fin 256, ValidCandidate (r.val + 12288) := by decide +kernel
#print axioms six_chunk_048
theorem six_chunk_049 : ∀ r : Fin 256, ValidCandidate (r.val + 12544) := by decide +kernel
#print axioms six_chunk_049
theorem six_chunk_050 : ∀ r : Fin 256, ValidCandidate (r.val + 12800) := by decide +kernel
#print axioms six_chunk_050
theorem six_chunk_051 : ∀ r : Fin 256, ValidCandidate (r.val + 13056) := by decide +kernel
#print axioms six_chunk_051
theorem six_chunk_052 : ∀ r : Fin 256, ValidCandidate (r.val + 13312) := by decide +kernel
#print axioms six_chunk_052
theorem six_chunk_053 : ∀ r : Fin 256, ValidCandidate (r.val + 13568) := by decide +kernel
#print axioms six_chunk_053
theorem six_chunk_054 : ∀ r : Fin 256, ValidCandidate (r.val + 13824) := by decide +kernel
#print axioms six_chunk_054
theorem six_chunk_055 : ∀ r : Fin 256, ValidCandidate (r.val + 14080) := by decide +kernel
#print axioms six_chunk_055
end Crown.SmallGraphs
