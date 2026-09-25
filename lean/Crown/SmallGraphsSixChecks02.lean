import Crown.SmallGraphsSixChecks01
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_016 : ∀ r : Fin 256, ValidCandidate (r.val + 4096) := by decide +kernel
#print axioms six_chunk_016
theorem six_chunk_017 : ∀ r : Fin 256, ValidCandidate (r.val + 4352) := by decide +kernel
#print axioms six_chunk_017
theorem six_chunk_018 : ∀ r : Fin 256, ValidCandidate (r.val + 4608) := by decide +kernel
#print axioms six_chunk_018
theorem six_chunk_019 : ∀ r : Fin 256, ValidCandidate (r.val + 4864) := by decide +kernel
#print axioms six_chunk_019
theorem six_chunk_020 : ∀ r : Fin 256, ValidCandidate (r.val + 5120) := by decide +kernel
#print axioms six_chunk_020
theorem six_chunk_021 : ∀ r : Fin 256, ValidCandidate (r.val + 5376) := by decide +kernel
#print axioms six_chunk_021
theorem six_chunk_022 : ∀ r : Fin 256, ValidCandidate (r.val + 5632) := by decide +kernel
#print axioms six_chunk_022
theorem six_chunk_023 : ∀ r : Fin 256, ValidCandidate (r.val + 5888) := by decide +kernel
#print axioms six_chunk_023
end Crown.SmallGraphs
