import Crown.SmallGraphsSixChecks12
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_104 : ∀ r : Fin 256, ValidCandidate (r.val + 26624) := by decide +kernel
#print axioms six_chunk_104
theorem six_chunk_105 : ∀ r : Fin 256, ValidCandidate (r.val + 26880) := by decide +kernel
#print axioms six_chunk_105
theorem six_chunk_106 : ∀ r : Fin 256, ValidCandidate (r.val + 27136) := by decide +kernel
#print axioms six_chunk_106
theorem six_chunk_107 : ∀ r : Fin 256, ValidCandidate (r.val + 27392) := by decide +kernel
#print axioms six_chunk_107
theorem six_chunk_108 : ∀ r : Fin 256, ValidCandidate (r.val + 27648) := by decide +kernel
#print axioms six_chunk_108
theorem six_chunk_109 : ∀ r : Fin 256, ValidCandidate (r.val + 27904) := by decide +kernel
#print axioms six_chunk_109
theorem six_chunk_110 : ∀ r : Fin 256, ValidCandidate (r.val + 28160) := by decide +kernel
#print axioms six_chunk_110
theorem six_chunk_111 : ∀ r : Fin 256, ValidCandidate (r.val + 28416) := by decide +kernel
#print axioms six_chunk_111
end Crown.SmallGraphs
