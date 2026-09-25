import Crown.SmallGraphsSixChecks07
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_064 : ∀ r : Fin 256, ValidCandidate (r.val + 16384) := by decide +kernel
#print axioms six_chunk_064
theorem six_chunk_065 : ∀ r : Fin 256, ValidCandidate (r.val + 16640) := by decide +kernel
#print axioms six_chunk_065
theorem six_chunk_066 : ∀ r : Fin 256, ValidCandidate (r.val + 16896) := by decide +kernel
#print axioms six_chunk_066
theorem six_chunk_067 : ∀ r : Fin 256, ValidCandidate (r.val + 17152) := by decide +kernel
#print axioms six_chunk_067
theorem six_chunk_068 : ∀ r : Fin 256, ValidCandidate (r.val + 17408) := by decide +kernel
#print axioms six_chunk_068
theorem six_chunk_069 : ∀ r : Fin 256, ValidCandidate (r.val + 17664) := by decide +kernel
#print axioms six_chunk_069
theorem six_chunk_070 : ∀ r : Fin 256, ValidCandidate (r.val + 17920) := by decide +kernel
#print axioms six_chunk_070
theorem six_chunk_071 : ∀ r : Fin 256, ValidCandidate (r.val + 18176) := by decide +kernel
#print axioms six_chunk_071
end Crown.SmallGraphs
