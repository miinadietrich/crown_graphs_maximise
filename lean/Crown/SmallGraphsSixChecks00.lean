import Crown.SmallGraphsSixCandidates
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_000 : ∀ r : Fin 256, ValidCandidate (r.val + 0) := by decide +kernel
#print axioms six_chunk_000
theorem six_chunk_001 : ∀ r : Fin 256, ValidCandidate (r.val + 256) := by decide +kernel
#print axioms six_chunk_001
theorem six_chunk_002 : ∀ r : Fin 256, ValidCandidate (r.val + 512) := by decide +kernel
#print axioms six_chunk_002
theorem six_chunk_003 : ∀ r : Fin 256, ValidCandidate (r.val + 768) := by decide +kernel
#print axioms six_chunk_003
theorem six_chunk_004 : ∀ r : Fin 256, ValidCandidate (r.val + 1024) := by decide +kernel
#print axioms six_chunk_004
theorem six_chunk_005 : ∀ r : Fin 256, ValidCandidate (r.val + 1280) := by decide +kernel
#print axioms six_chunk_005
theorem six_chunk_006 : ∀ r : Fin 256, ValidCandidate (r.val + 1536) := by decide +kernel
#print axioms six_chunk_006
theorem six_chunk_007 : ∀ r : Fin 256, ValidCandidate (r.val + 1792) := by decide +kernel
#print axioms six_chunk_007
end Crown.SmallGraphs
