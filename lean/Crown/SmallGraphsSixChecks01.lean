import Crown.SmallGraphsSixChecks00
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_008 : ∀ r : Fin 256, ValidCandidate (r.val + 2048) := by decide +kernel
#print axioms six_chunk_008
theorem six_chunk_009 : ∀ r : Fin 256, ValidCandidate (r.val + 2304) := by decide +kernel
#print axioms six_chunk_009
theorem six_chunk_010 : ∀ r : Fin 256, ValidCandidate (r.val + 2560) := by decide +kernel
#print axioms six_chunk_010
theorem six_chunk_011 : ∀ r : Fin 256, ValidCandidate (r.val + 2816) := by decide +kernel
#print axioms six_chunk_011
theorem six_chunk_012 : ∀ r : Fin 256, ValidCandidate (r.val + 3072) := by decide +kernel
#print axioms six_chunk_012
theorem six_chunk_013 : ∀ r : Fin 256, ValidCandidate (r.val + 3328) := by decide +kernel
#print axioms six_chunk_013
theorem six_chunk_014 : ∀ r : Fin 256, ValidCandidate (r.val + 3584) := by decide +kernel
#print axioms six_chunk_014
theorem six_chunk_015 : ∀ r : Fin 256, ValidCandidate (r.val + 3840) := by decide +kernel
#print axioms six_chunk_015
end Crown.SmallGraphs
